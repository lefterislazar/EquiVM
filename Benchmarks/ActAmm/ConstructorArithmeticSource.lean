import Benchmarks.ActAmm.ConstructorSecondCallSource
import Benchmarks.ActAmm.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem ammCtorEvalInitialBalance0
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      { contract := contract,
        locals := ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm (.var "initialBalance0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (ret2.extract 0 32)))) := by
  simp only [evalExpr?, ammCtorAfterInitialBalance0Locals, store_get_self,
    EvalResult.ofOption]

theorem ammCtorEvalInitialBalance1
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      { contract := contract,
        locals := ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm (.var "initialBalance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (ret1.extract 0 32)))) := by
  simp only [evalExpr?, ammCtorAfterInitialBalance0Locals]
  rw [store_get_ne (ammCtorAfterInitialBalance1Locals t0 t1 liquidity ret1)
    (k := "initialBalance0") (a := "initialBalance1") _ (by decide)]
  simp only [ammCtorAfterInitialBalance1Locals, store_get_self,
    EvalResult.ofOption]

theorem ammCtorEvalInitialProductOk
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hfit : (fromByteArrayBigEndian (ret2.extract 0 32)) *
      (fromByteArrayBigEndian (ret1.extract 0 32)) < UInt256.size) :
    evalExpr? config
      { contract := contract,
        locals := ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm (checkedMul (.var "initialBalance0") (.var "initialBalance1")) =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (ret2.extract 0 32)) *
          (fromByteArrayBigEndian (ret1.extract 0 32))))) := by
  exact ammEvalCheckedMul_ok
    (ammCtorEvalInitialBalance0 t0 t1 liquidity ret1 ret2 evm)
    (ammCtorEvalInitialBalance1 t0 t1 liquidity ret1 ret2 evm) hfit

theorem ammCtorEvalInitialProductOverflow
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32))) :
    evalExpr? config
      { contract := contract,
        locals := ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm (checkedMul (.var "initialBalance0") (.var "initialBalance1")) =
      .revert := by
  exact ammEvalCheckedMul_revert
    (ammCtorEvalInitialBalance0 t0 t1 liquidity ret1 ret2 evm)
    (ammCtorEvalInitialBalance1 t0 t1 liquidity ret1 ret2 evm) hover

def ammCtorAfterProductLocals
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) : Store :=
  (ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2).insert
    "balanceProduct" (.int (Int.ofNat
      ((fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32)))))

theorem ammCtorProductStmtOk
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hfit : (fromByteArrayBigEndian (ret2.extract 0 32)) *
      (fromByteArrayBigEndian (ret1.extract 0 32)) < UInt256.size) :
    ExecStmt config
      { contract := contract,
        locals := ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm
      (.letDecl "balanceProduct" (some uint256)
        (checkedMul (.var "initialBalance0") (.var "initialBalance1")))
      (.ok ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm) := by
  simpa [ammCtorAfterProductLocals] using
    (ExecStmt.letDecl (ammCtorEvalInitialProductOk t0 t1 liquidity ret1 ret2 evm hfit))

theorem ammCtorProductStmtOverflow
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32))) :
    ExecStmt config
      { contract := contract,
        locals := ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm
      (.letDecl "balanceProduct" (some uint256)
        (checkedMul (.var "initialBalance0") (.var "initialBalance1")))
      .reverted := by
  exact ExecStmt.letDeclRevert
    (ammCtorEvalInitialProductOverflow t0 t1 liquidity ret1 ret2 evm hover)

theorem ammCtorEvalLiquidityAfterProduct
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      { contract := contract,
        locals := ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm (.var "liquidity") = .ok (.int liquidity) := by
  simp only [evalExpr?, ammCtorAfterProductLocals,
    ammCtorAfterInitialBalance0Locals,
    ammCtorAfterInitialBalance1Locals,
    ammCtorAfterBaseLocals]
  rw [store_get_ne _ (k := "balanceProduct") (a := "liquidity") _ (by decide)]
  rw [store_get_ne _ (k := "initialBalance0") (a := "liquidity") _ (by decide)]
  rw [store_get_ne _ (k := "initialBalance1") (a := "liquidity") _ (by decide)]
  rw [store_get_ne _ (k := "baseSupply") (a := "liquidity") _ (by decide)]
  simpa only [evalExpr?] using ammCtorEvalLiquidity t0 t1 liquidity evm

theorem ammCtorEvalLiquiditySquareOk
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity)
    (hfit : liquidity.toNat * liquidity.toNat < UInt256.size) :
    evalExpr? config
      { contract := contract,
        locals := ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm (checkedMul (.var "liquidity") (.var "liquidity")) =
      .ok (.int (Int.ofNat (liquidity.toNat * liquidity.toNat))) := by
  have hliq := ammCtorEvalLiquidityAfterProduct t0 t1 liquidity ret1 ret2 evm
  have hval : (Value.int liquidity) = .int (Int.ofNat liquidity.toNat) :=
    congrArg Value.int (Int.toNat_of_nonneg h0).symm
  have hliqNat : evalExpr? config
      ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.var "liquidity") = .ok (.int (Int.ofNat liquidity.toNat)) := by
    rw [hval] at hliq
    exact hliq
  exact ammEvalCheckedMul_ok (cfg := config)
    (frame := ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (x := .var "liquidity") (y := .var "liquidity")
    (a := liquidity.toNat) (b := liquidity.toNat) hliqNat hliqNat hfit

theorem ammCtorEvalLiquiditySquareOverflow
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity)
    (hover : UInt256.size ≤ liquidity.toNat * liquidity.toNat) :
    evalExpr? config
      { contract := contract,
        locals := ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm (checkedMul (.var "liquidity") (.var "liquidity")) = .revert := by
  have hliq := ammCtorEvalLiquidityAfterProduct t0 t1 liquidity ret1 ret2 evm
  have hval : (Value.int liquidity) = .int (Int.ofNat liquidity.toNat) :=
    congrArg Value.int (Int.toNat_of_nonneg h0).symm
  have hliqNat : evalExpr? config
      ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.var "liquidity") = .ok (.int (Int.ofNat liquidity.toNat)) := by
    rw [hval] at hliq
    exact hliq
  exact ammEvalCheckedMul_revert (cfg := config)
    (frame := ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (x := .var "liquidity") (y := .var "liquidity")
    (a := liquidity.toNat) (b := liquidity.toNat) hliqNat hliqNat hover

def ammCtorAfterSquareLocals
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) : Store :=
  (ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2).insert
    "liquiditySquared" (.int (Int.ofNat (liquidity.toNat * liquidity.toNat)))

theorem ammCtorSquareStmtOk
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity)
    (hfit : liquidity.toNat * liquidity.toNat < UInt256.size) :
    ExecStmt config
      { contract := contract,
        locals := ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm
      (.letDecl "liquiditySquared" (some uint256)
        (checkedMul (.var "liquidity") (.var "liquidity")))
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm) := by
  simpa [ammCtorAfterSquareLocals] using
    (ExecStmt.letDecl
      (ammCtorEvalLiquiditySquareOk t0 t1 liquidity ret1 ret2 evm h0 hfit))

theorem ammCtorSquareStmtOverflow
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity)
    (hover : UInt256.size ≤ liquidity.toNat * liquidity.toNat) :
    ExecStmt config
      { contract := contract,
        locals := ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm
      (.letDecl "liquiditySquared" (some uint256)
        (checkedMul (.var "liquidity") (.var "liquidity")))
      .reverted := by
  exact ExecStmt.letDeclRevert
    (ammCtorEvalLiquiditySquareOverflow t0 t1 liquidity ret1 ret2 evm h0 hover)

theorem ammSolmCtorExecReverts_productOverflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm2 : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32)))
    (hprefix : ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"])
      (.ok ⟨contract, ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := ammCtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm (((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        (.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))) :: _)
      .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert
        (ammCtorProductStmtOverflow t0 t1 liquidity ret1 ret2 evm2 hover))

theorem ammCtorSourceProductSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm2 : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hfit : (fromByteArrayBigEndian (ret2.extract 0 32)) *
      (fromByteArrayBigEndian (ret1.extract 0 32)) < UInt256.size)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"])
      (.ok ⟨contract, ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))])
      (.ok ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
  have htail : ExecBlock config
      ⟨contract, ammCtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2⟩
      evm2 [.letDecl "balanceProduct" (some uint256)
        (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]
      (.ok ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
    simpa only [collapseReturns] using
      (ExecBlock.consNormal
        (ammCtorProductStmtOk t0 t1 liquidity ret1 ret2 evm2 hfit)
        ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem ammSolmCtorExecReverts_squareOverflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm2 : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity)
    (hover : UInt256.size ≤ liquidity.toNat * liquidity.toNat)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))])
      (.ok ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := ammCtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm ((((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        (.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))) :: _)
      .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert
        (ammCtorSquareStmtOverflow t0 t1 liquidity ret1 ret2 evm2 h0 hover))

theorem ammCtorSourceSquareSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm2 : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity)
    (hfit : liquidity.toNat * liquidity.toNat < UInt256.size)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))])
      (.ok ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))]))
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
  have htail : ExecBlock config
      ⟨contract, ammCtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩
      evm2 [.letDecl "liquiditySquared" (some uint256)
        (checkedMul (.var "liquidity") (.var "liquidity"))]
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
    simpa only [collapseReturns] using
      (ExecBlock.consNormal
        (ammCtorSquareStmtOk t0 t1 liquidity ret1 ret2 evm2 h0 hfit)
        ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem ammCtorEvalProductLocal
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.var "balanceProduct") =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (ret2.extract 0 32)) *
          (fromByteArrayBigEndian (ret1.extract 0 32))))) := by
  simp only [evalExpr?, ammCtorAfterSquareLocals]
  rw [store_get_ne _ (k := "liquiditySquared") (a := "balanceProduct") _ (by decide)]
  simp only [ammCtorAfterProductLocals, store_get_self, EvalResult.ofOption]

theorem ammCtorEvalSquareLocal
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.var "liquiditySquared") =
      .ok (.int (Int.ofNat (liquidity.toNat * liquidity.toNat))) := by
  simp only [evalExpr?, ammCtorAfterSquareLocals, store_get_self,
    EvalResult.ofOption]

theorem ammCtorEvalProductEqTrue
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (heq : liquidity.toNat * liquidity.toNat =
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32))) :
    evalExpr? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")) =
      .ok (.bool true) := by
  simp only [evalExpr?, ammCtorEvalSquareLocal,
    ammCtorEvalProductLocal, EvalResult.bind, bind, evalBinaryOp?]
  rw [heq]
  simp

theorem ammCtorEvalProductEqFalse
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hne : liquidity.toNat * liquidity.toNat ≠
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32))) :
    evalExpr? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")) =
      .ok (.bool false) := by
  have hneValue :
      Value.int (Int.ofNat (liquidity.toNat * liquidity.toNat)) ≠
        Value.int (Int.ofNat
          ((fromByteArrayBigEndian (ret2.extract 0 32)) *
            (fromByteArrayBigEndian (ret1.extract 0 32)))) := by
    intro hv
    apply hne
    have hi := Value.int.inj hv
    exact Int.ofNat.inj hi
  simp only [evalExpr?, ammCtorEvalSquareLocal,
    ammCtorEvalProductLocal, EvalResult.bind, bind, evalBinaryOp?]
  rw [beq_false_of_ne hneValue]

theorem ammSolmCtorExecReverts_productMismatch
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm2 : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hne : liquidity.toNat * liquidity.toNat ≠
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32)))
    (hprefix : ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))]))
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := ammCtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm ((((((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))])) ++
        (.require (.binary .eq (.var "liquiditySquared") (.var "balanceProduct"))) :: _)
      .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.requireFalse
        (ammCtorEvalProductEqFalse t0 t1 liquidity ret1 ret2 evm2 hne)))

theorem ammCtorEvalLiquidityAfterSquare
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.var "liquidity") = .ok (.int liquidity) := by
  simp only [evalExpr?, ammCtorAfterSquareLocals]
  rw [store_get_ne _ (k := "liquiditySquared") (a := "liquidity") _ (by decide)]
  simpa only [evalExpr?] using
    ammCtorEvalLiquidityAfterProduct t0 t1 liquidity ret1 ret2 evm

theorem ammCtorEvalPositiveAfterSquare
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hpos : 0 < liquidity) :
    evalExpr? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.binary .gt (.var "liquidity") (.intLit 0)) =
      .ok (.bool true) := by
  simp only [evalExpr?, ammCtorEvalLiquidityAfterSquare,
    EvalResult.bind, bind, evalBinaryOp?]
  simp [hpos]

theorem ammCtorSourceGuardsSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm2 : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (heq : liquidity.toNat * liquidity.toNat =
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32)))
    (hpos : 0 < liquidity)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))]))
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((((((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))])) ++
        [.require (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")),
         .require (.binary .gt (.var "liquidity") (.intLit 0))])
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
  have htail : ExecBlock config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2
      [.require (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")),
       .require (.binary .gt (.var "liquidity") (.intLit 0))]
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
    apply ExecBlock.consNormal
      (ExecStmt.requireTrue
        (ammCtorEvalProductEqTrue t0 t1 liquidity ret1 ret2 evm2 heq))
    apply ExecBlock.consNormal
      (ExecStmt.requireTrue
        (ammCtorEvalPositiveAfterSquare t0 t1 liquidity ret1 ret2 evm2 hpos))
    exact ExecBlock.nil
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm
