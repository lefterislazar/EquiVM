{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}

-- | Solver-free, single-path symbolic execution.
--
-- The result deliberately mirrors the cursor carried by EquiVM's @RD@:
-- the final VM contains pc, stack, memory/active words, returndata and the
-- account world, while this wrapper records the step and gas-cost indices.
module SymCheck.StraightLine
  ( StraightLineStop(..)
  , BranchSuccessors(..)
  , InitialStackSpec(..)
  , AbstractStackSummary(..)
  , StraightLineSummary(..)
  , runStraightLine
  , runStraightLineWithStack
  ) where

import Control.Monad.ST (RealWorld, ST)
import Control.Monad.Trans.State.Strict (runStateT)
import Data.ByteString qualified as BS
import Data.Text qualified as T
import Data.Word (Word8)
import EVM (exec1)
import EVM.Expr qualified as Expr
import EVM.Op (getOp)
import EVM.Types
import EVM.Types qualified as FrameStateRecord (FrameState(..))
import EVM.Types qualified as VMRecord (VM(..))
import SymCheck.Midpoint
  ( SegmentRunSpec(..)
  , opcodeProducedStackDepth
  , opcodeRequiredStackDepth
  )

data StraightLineStop
  = StraightLineTargetPc Int
  | StraightLineFuelExhausted
  | StraightLineHalted (VMResult Symbolic)
  | StraightLineNeedsSmt (Expr EWord)
  | StraightLineNeedsConcreteValue (Expr EWord)
  | StraightLineNeedsExternalData String
  | StraightLineNeedsBranch
  | StraightLineCallBoundary String
  | StraightLineStackUnderflow Int Int
  | StraightLineStackOverflow Int
  | StraightLineInfeasibleStackBounds Int Int
  deriving (Show)

data BranchSuccessors = BranchSuccessors
  { branchNotTakenAddress :: Int
  , branchTakenAddress :: Expr EWord
  } deriving (Show)

-- | The explicitly supplied stack is a known prefix above an abstract initial
-- tail.  Supplying an exact total depth makes underflow and overflow concrete;
-- otherwise the executor derives a valid interval for the initial depth.
data InitialStackSpec = InitialStackSpec
  { stackExactInitialDepth :: Maybe Int
  } deriving (Show)

data AbstractStackSummary = AbstractStackSummary
  { stackKnownPrefixDepth :: Int
  , stackMaterializedTailDepth :: Int
  , stackMinimumInitialDepth :: Int
  , stackMaximumInitialDepth :: Int
  , stackExactDepth :: Maybe Int
  } deriving (Show)

data StraightLineSummary = StraightLineSummary
  { summarySteps :: Int
  , summaryGasCost :: Expr EWord
  , summaryPcTrace :: [Int]
  , summaryStopReason :: StraightLineStop
  , summaryBranchSuccessors :: Maybe BranchSuccessors
  , summaryStack :: AbstractStackSummary
  , summaryFinalVm :: VM Symbolic
  }

data StackTracker = StackTracker
  { trackerKnownPrefixDepth :: Int
  , trackerMaterializedTailDepth :: Int
  , trackerHeightDelta :: Int
  , trackerMinimumInitialDepth :: Int
  , trackerMaximumInitialDepth :: Int
  , trackerExactDepth :: Maybe Int
  }

-- | Execute one path without constructing or consulting an SMT solver.
--
-- A locally decidable 'PleaseAskSMT' request is resumed when simplification
-- reduces its condition to a literal.  For every other unresolved effect we
-- return the VM from before the opcode, so the reported cursor, step count and
-- gas cost describe only completed instructions (as RD's @k@ and @C@ do).
runStraightLine :: SegmentRunSpec -> VM Symbolic -> ST RealWorld StraightLineSummary
runStraightLine spec =
  runStraightLineWithStack spec InitialStackSpec {stackExactInitialDepth = Nothing}

runStraightLineWithStack
  :: SegmentRunSpec
  -> InitialStackSpec
  -> VM Symbolic
  -> ST RealWorld StraightLineSummary
runStraightLineWithStack spec stackSpec vm0 = go [] 0 spec.fuel initialTracker vm0
  where
    initialBurned = vm0.burned
    knownPrefixDepth = length vm0.state.stack
    initialTracker =
      StackTracker
        { trackerKnownPrefixDepth = knownPrefixDepth
        , trackerMaterializedTailDepth = 0
        , trackerHeightDelta = 0
        , trackerMinimumInitialDepth = knownPrefixDepth
        , trackerMaximumInitialDepth = 1024
        , trackerExactDepth = stackSpec.stackExactInitialDepth
        }

    finish traceRev stepsDone tracker reason vm =
      pure StraightLineSummary
        { summarySteps = stepsDone
        , summaryGasCost = Expr.simplify (Expr.sub vm.burned initialBurned)
        , summaryPcTrace = finishPcTrace traceRev vm.state.pc
        , summaryStopReason = reason
        , summaryBranchSuccessors = branchSuccessors reason vm
        , summaryStack = stackSummary tracker
        , summaryFinalVm = vm
        }

    go traceRev stepsDone fuelLeft tracker vm
      | Just exactDepth <- tracker.trackerExactDepth
      , exactDepth < tracker.trackerKnownPrefixDepth =
          finish traceRev stepsDone tracker
            (StraightLineStackUnderflow tracker.trackerKnownPrefixDepth exactDepth) vm
      | Just exactDepth <- tracker.trackerExactDepth
      , exactDepth > 1024 =
          finish traceRev stepsDone tracker (StraightLineStackOverflow exactDepth) vm
      | tracker.trackerMinimumInitialDepth > tracker.trackerMaximumInitialDepth =
          finish traceRev stepsDone tracker
            (StraightLineInfeasibleStackBounds
              tracker.trackerMinimumInitialDepth
              tracker.trackerMaximumInitialDepth)
            vm
      | Just stopPc <- spec.targetPc
      , vm.state.pc == stopPc =
          finish traceRev stepsDone tracker (StraightLineTargetPc stopPc) vm
      | Just result <- vm.result =
          finish traceRev stepsDone tracker (classifyResult result) vm
      | fuelLeft <= 0 =
          finish traceRev stepsDone tracker StraightLineFuelExhausted vm
      | otherwise =
          case prepareStackForCurrentOpcode tracker vm of
            Left reason -> finish traceRev stepsDone tracker reason vm
            Right (preparedTracker, preparedVm, maybeOp) ->
              case callOrCreateBoundary preparedVm of
                Just opcode ->
                  finish traceRev stepsDone preparedTracker
                    (StraightLineCallBoundary opcode) preparedVm
                Nothing ->
                  case checkPredictedOverflow preparedTracker maybeOp of
                    Left reason ->
                      finish traceRev stepsDone preparedTracker reason preparedVm
                    Right boundedTracker -> do
                      (_, attemptedVm) <- runStateT (exec1 spec.config) preparedVm
                      resolveLocalEffects attemptedVm >>= \case
                        Left reason ->
                          finish traceRev stepsDone boundedTracker reason preparedVm
                        Right completedVm ->
                          let actualDelta =
                                length completedVm.state.stack - length preparedVm.state.stack
                              completedTracker =
                                boundedTracker
                                  { trackerHeightDelta =
                                      boundedTracker.trackerHeightDelta + actualDelta
                                  }
                          in go
                              (extendPcTrace traceRev preparedVm.state.pc)
                              (stepsDone + 1)
                              (fuelLeft - 1)
                              completedTracker
                              completedVm

    -- Resolving one literal query can expose another effect from the same
    -- opcode.  Recur until the opcode really finishes or reaches a boundary.
    resolveLocalEffects attemptedVm =
      case attemptedVm.result of
        Just (HandleEffect (Query (PleaseAskSMT condition _ continue))) ->
          case Expr.simplify condition of
            Lit value -> do
              (_, resumedVm) <- runStateT (continue (Case (value /= 0))) attemptedVm
              resolveLocalEffects resumedVm
            simplifiedCondition ->
              pure (Left (StraightLineNeedsSmt simplifiedCondition))
        Just effectResult@(HandleEffect _) ->
          pure (Left (classifyResult effectResult))
        _ -> pure (Right attemptedVm)

stackSummary :: StackTracker -> AbstractStackSummary
stackSummary tracker =
  AbstractStackSummary
    { stackKnownPrefixDepth = tracker.trackerKnownPrefixDepth
    , stackMaterializedTailDepth = tracker.trackerMaterializedTailDepth
    , stackMinimumInitialDepth = tracker.trackerMinimumInitialDepth
    , stackMaximumInitialDepth = tracker.trackerMaximumInitialDepth
    , stackExactDepth = tracker.trackerExactDepth
    }

branchSuccessors :: StraightLineStop -> VM Symbolic -> Maybe BranchSuccessors
branchSuccessors reason vm =
  case (isUnresolvedBranchStop reason, currentOpcode vm, vm.state.stack) of
    (True, Just OpJumpi, target : _) ->
      Just
        BranchSuccessors
          { branchNotTakenAddress = vm.state.pc + 1
          , branchTakenAddress = Expr.simplify target
          }
    _ -> Nothing

isUnresolvedBranchStop :: StraightLineStop -> Bool
isUnresolvedBranchStop = \case
  StraightLineNeedsSmt _ -> True
  StraightLineNeedsConcreteValue _ -> True
  StraightLineNeedsBranch -> True
  _ -> False

prepareStackForCurrentOpcode
  :: StackTracker
  -> VM Symbolic
  -> Either StraightLineStop (StackTracker, VM Symbolic, Maybe (GenericOp Word8))
prepareStackForCurrentOpcode tracker vm =
  case currentOpcode vm of
    Nothing -> Right (tracker, vm, Nothing)
    Just op ->
      let required = opcodeRequiredStackDepth op
          missing = max 0 (required - length vm.state.stack)
          materialized0 = tracker.trackerMaterializedTailDepth
          materialized1 = materialized0 + missing
          minimum1 =
            max tracker.trackerMinimumInitialDepth
              (tracker.trackerKnownPrefixDepth + materialized1)
      in case tracker.trackerExactDepth of
          Just exactDepth
            | minimum1 > exactDepth ->
                Left (StraightLineStackUnderflow minimum1 exactDepth)
          _
            | minimum1 > tracker.trackerMaximumInitialDepth ->
                Left
                  (StraightLineInfeasibleStackBounds
                    minimum1 tracker.trackerMaximumInitialDepth)
            | otherwise ->
                let freshItems =
                      [ Var (T.pack ("initial_stack_" <> show idx))
                      | idx <- [materialized0 .. materialized1 - 1]
                      ]
                    state' =
                      vm.state
                        { FrameStateRecord.stack = vm.state.stack <> freshItems }
                    vm' = vm {VMRecord.state = state'}
                    tracker' =
                      tracker
                        { trackerMaterializedTailDepth = materialized1
                        , trackerMinimumInitialDepth = minimum1
                        }
                in Right (tracker', vm', Just op)

checkPredictedOverflow
  :: StackTracker
  -> Maybe (GenericOp Word8)
  -> Either StraightLineStop StackTracker
checkPredictedOverflow tracker = \case
  Nothing -> Right tracker
  Just op ->
    let opcodeDelta = opcodeProducedStackDepth op - opcodeRequiredStackDepth op
        nextHeightDelta = tracker.trackerHeightDelta + opcodeDelta
        maximumForStep = min 1024 (1024 - nextHeightDelta)
        maximum1 = min tracker.trackerMaximumInitialDepth maximumForStep
    in case tracker.trackerExactDepth of
        Just exactDepth
          | exactDepth > maximum1 ->
              Left (StraightLineStackOverflow (exactDepth + nextHeightDelta))
        _
          | tracker.trackerMinimumInitialDepth > maximum1 ->
              Left
                (StraightLineInfeasibleStackBounds
                  tracker.trackerMinimumInitialDepth maximum1)
          | otherwise ->
              Right tracker {trackerMaximumInitialDepth = maximum1}

classifyResult :: VMResult Symbolic -> StraightLineStop
classifyResult = \case
  HandleEffect (Query query0) ->
    case query0 of
      PleaseAskSMT condition _ _ -> StraightLineNeedsSmt (Expr.simplify condition)
      PleaseGetSols expr _ _ _ -> StraightLineNeedsConcreteValue (Expr.simplify expr)
      PleaseFetchContract {} -> StraightLineNeedsExternalData "contract"
      PleaseFetchSlot {} -> StraightLineNeedsExternalData "storage slot"
      PleaseDoFFI {} -> StraightLineNeedsExternalData "FFI result"
      PleaseReadEnv {} -> StraightLineNeedsExternalData "environment variable"
  HandleEffect (Branch _) -> StraightLineNeedsBranch
  result -> StraightLineHalted result

callOrCreateBoundary :: VM Symbolic -> Maybe String
callOrCreateBoundary vm = do
  op <- currentOpcode vm
  case op of
    OpCall -> Just "CALL"
    OpCallcode -> Just "CALLCODE"
    OpDelegatecall -> Just "DELEGATECALL"
    OpStaticcall -> Just "STATICCALL"
    OpCreate -> Just "CREATE"
    OpCreate2 -> Just "CREATE2"
    _ -> Nothing

currentOpcode :: VM Symbolic -> Maybe (GenericOp Word8)
currentOpcode vm = do
  codeBytes <-
    case vm.state.code of
      RuntimeCode (ConcreteRuntimeCode bytes) -> Just bytes
      InitCode bytes _ -> Just bytes
      _ -> Nothing
  if vm.state.pc < 0 || vm.state.pc >= BS.length codeBytes
    then Nothing
    else Just (getOp (BS.index codeBytes vm.state.pc))

extendPcTrace :: [Int] -> Int -> [Int]
extendPcTrace traceRev pc0 =
  case traceRev of
    pc1 : _ | pc1 == pc0 -> traceRev
    _ -> pc0 : traceRev

finishPcTrace :: [Int] -> Int -> [Int]
finishPcTrace traceRev pc0 =
  reverse (extendPcTrace traceRev pc0)
