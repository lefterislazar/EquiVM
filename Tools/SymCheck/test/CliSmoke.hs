module Main (main) where

import Data.List (isInfixOf)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

data TestCase = TestCase
  { testName :: String
  , testArgs :: [String]
  , expectedExit :: ExitCode
  , expectedStdout :: [String]
  , expectedStderr :: [String]
  }

main :: IO ()
main =
  mapM_ runTest tests

tests :: [TestCase]
tests =
  [ TestCase
      { testName = "cli-pre-post-qed"
      , testArgs =
          [ "run"
          , "--code", "600160020100"
          , "--pc", "2"
          , "--stack", "var:x"
          , "--fuel", "3"
          , "--pre", "stack[0]==1"
          , "--post", "stack[0]==3"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "postconditions:"
          , "=> qed"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-post-cex"
      , testArgs =
          [ "run"
          , "--code", "600160020100"
          , "--pc", "2"
          , "--stack", "0x1"
          , "--fuel", "3"
          , "--pre", "stack[0]==1"
          , "--post", "stack[0]==4"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "postconditions:"
          , "=> cex"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-invalid-precondition"
      , testArgs =
          [ "run"
          , "--code", "600160020100"
          , "--pc", "2"
          , "--stack", "0x1"
          , "--fuel", "3"
          , "--pre", "pc==2"
          ]
      , expectedExit = ExitFailure 1
      , expectedStdout = []
      , expectedStderr =
          [ "pc preconditions are not supported; set --pc directly"
          ]
      }
  , TestCase
      { testName = "cli-straight-line-summary"
      , testArgs =
          [ "summarize"
          , "--code", "600160020100"
          , "--pc", "2"
          , "--stack", "0x1"
          , "--fuel", "3"
          , "--active-words", "2"
          , "--gas", "100"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "summary: straight-line (solver-free)"
          , "steps: 3"
          , "gas-cost: 6"
          , "gas-available: 94"
          , "stack: [3]"
          , "active-words: 2"
          , "returndata:"
          , "storage:"
          , "transient-storage:"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-straight-line-symbolic-branch"
      , testArgs =
          [ "summarize"
          , "--code", "000057005b00"
          , "--pc", "2"
          , "--stack", "4"
          , "--stack", "var:c"
          , "--fuel", "5"
          , "--gas", "100"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "steps: 0"
          , "gas-cost: 0"
          , "gas-available: 100"
          , "needs SMT at current opcode"
          , "next-addresses: [not-taken=3, taken=4]"
          , "pc:    2"
          , "stack: [4, (Var \"c\")]"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-straight-line-symbolic-branch-json"
      , testArgs =
          [ "summarize"
          , "--code", "000057005b00"
          , "--pc", "2"
          , "--stack", "4"
          , "--stack", "var:c"
          , "--fuel", "5"
          , "--json"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "\"nextAddresses\""
          , "\"notTaken\":3"
          , "\"taken\":\"4\""
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-straight-line-call-boundary"
      , testArgs =
          [ "summarize"
          , "--code", "f100"
          , "--fuel", "2"
          , "--stack", "5"
          , "--stack", "0x1234"
          , "--stack", "0"
          , "--stack", "0"
          , "--stack", "0"
          , "--stack", "0"
          , "--stack", "0"
          , "--gas", "100000"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "steps: 0"
          , "gas-cost: 0"
          , "call/create boundary at current opcode (CALL)"
          , "pc:    0"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-straight-line-abstract-stack-tail"
      , testArgs =
          [ "summarize"
          , "--code", "0100"
          , "--fuel", "2"
          , "--gas", "100"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "steps: 2"
          , "Var \"initial_stack_0\""
          , "Var \"initial_stack_1\""
          , "++ drop 2 initial-stack-tail"
          , "initial-stack-depth: 2 <= depth <= 1024"
          , "materialized-initial-tail: 2"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-straight-line-exact-stack-underflow"
      , testArgs =
          [ "summarize"
          , "--code", "0100"
          , "--fuel", "2"
          , "--stack-depth", "1"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "steps: 0"
          , "stack underflow at current opcode"
          , "requires initial depth 2, exact depth is 1"
          , "initial-stack-depth: 1 (exact)"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-straight-line-exact-stack-overflow"
      , testArgs =
          [ "summarize"
          , "--code", "5f"
          , "--fuel", "1"
          , "--stack-depth", "1024"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "steps: 0"
          , "stack overflow at current opcode"
          , "resulting depth 1025 exceeds 1024"
          , "initial-stack-depth: 1024 (exact)"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-straight-line-symbolic-stack-overflow-bound"
      , testArgs =
          [ "summarize"
          , "--code", "5f"
          , "--fuel", "1"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "steps: 1"
          , "stack: [0] ++ drop 0 initial-stack-tail"
          , "initial-stack-depth: 0 <= depth <= 1023"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-straight-line-materializes-after-jump"
      , testArgs =
          [ "summarize"
          , "--code", "600456005b0100"
          , "--fuel", "5"
          , "--gas", "100"
          , "--trace-opcodes"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "steps: 5"
          , "[0:PUSH1, 2:JUMP, 4:JUMPDEST, 5:ADD, 6:STOP]"
          , "Var \"initial_stack_0\""
          , "Var \"initial_stack_1\""
          , "initial-stack-depth: 2 <= depth <= 1023"
          ]
      , expectedStderr = []
      }
  ]

runTest :: TestCase -> IO ()
runTest test = do
  (exitCode, stdoutText, stderrText) <- readProcessWithExitCode "symcheck" (testArgs test) ""
  assertEqual (testName test) "exit code" (expectedExit test) exitCode stderrText
  mapM_ (assertContains (testName test) stdoutText) (expectedStdout test)
  mapM_ (assertContains (testName test) stderrText) (expectedStderr test)
  case testArgs test of
    "summarize" : _ ->
      mapM_ (assertNotContains (testName test) stdoutText) summaryForbiddenOutput
    _ -> pure ()

summaryForbiddenOutput :: [String]
summaryForbiddenOutput =
  [ "\nworld:"
  , "\ncreated-accounts:"
  , "\naddress:"
  , "\ncode-address:"
  , "\ncaller:"
  , "\norigin:"
  , "\ncoinbase:"
  , "\ncalldata:"
  , "\ncallvalue:"
  , "\nblock-number:"
  , "\ntimestamp:"
  , "\nchain-id:"
  , "\nstatic:"
  , "\noriginal-storage:"
  , "\"world\":"
  , "\"createdAccounts\":"
  , "\"environment\":"
  , "\"originalStorage\":"
  ]

assertEqual :: (Eq a, Show a) => String -> String -> a -> a -> String -> IO ()
assertEqual name field expected actual context =
  if expected == actual
    then pure ()
    else fail $
      name
        <> ": unexpected "
        <> field
        <> "\nexpected: "
        <> show expected
        <> "\nactual:   "
        <> show actual
        <> renderContext context

assertContains :: String -> String -> String -> IO ()
assertContains name haystack needle =
  if needle `isInfixOf` haystack
    then pure ()
    else fail $
      name
        <> ": expected stdout to contain "
        <> show needle
        <> "\nactual stdout:\n"
        <> haystack

assertNotContains :: String -> String -> String -> IO ()
assertNotContains name haystack needle =
  if needle `isInfixOf` haystack
    then fail $
      name
        <> ": expected stdout not to contain "
        <> show needle
        <> "\nactual stdout:\n"
        <> haystack
    else pure ()

renderContext :: String -> String
renderContext context
  | null context = ""
  | otherwise = "\ncontext:\n" <> context
