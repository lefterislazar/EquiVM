import Benchmarks.ActAmm4.ConstructorSecondCallSource
import Benchmarks.ActAmm4.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorEvalInitialBalance0
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm (.var "initialBalance0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (ret2.extract 0 32)))) := by
  simp only [evalExpr?, amm4CtorAfterInitialBalance0Locals, store_get_self,
    EvalResult.ofOption]

theorem amm4CtorEvalInitialBalance1
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm (.var "initialBalance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (ret1.extract 0 32)))) := by
  simp only [evalExpr?, amm4CtorAfterInitialBalance0Locals]
  rw [store_get_ne (amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1)
    (k := "initialBalance0") (a := "initialBalance1") _ (by decide)]
  simp only [amm4CtorAfterInitialBalance1Locals, store_get_self,
    EvalResult.ofOption]

theorem amm4CtorEvalInitialProductOk
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hfit : (fromByteArrayBigEndian (ret2.extract 0 32)) *
      (fromByteArrayBigEndian (ret1.extract 0 32)) < UInt256.size) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm (checkedMul (.var "initialBalance0") (.var "initialBalance1")) =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (ret2.extract 0 32)) *
          (fromByteArrayBigEndian (ret1.extract 0 32))))) := by
  exact amm4EvalCheckedMul_ok
    (amm4CtorEvalInitialBalance0 t0 t1 liquidity ret1 ret2 evm)
    (amm4CtorEvalInitialBalance1 t0 t1 liquidity ret1 ret2 evm) hfit

theorem amm4CtorEvalInitialProductOverflow
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32))) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm (checkedMul (.var "initialBalance0") (.var "initialBalance1")) =
      .revert := by
  exact amm4EvalCheckedMul_revert
    (amm4CtorEvalInitialBalance0 t0 t1 liquidity ret1 ret2 evm)
    (amm4CtorEvalInitialBalance1 t0 t1 liquidity ret1 ret2 evm) hover

def amm4CtorAfterProductLocals
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) : Store :=
  (amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2).insert
    "balanceProduct" (.int (Int.ofNat
      ((fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32)))))

theorem amm4CtorProductStmtOk
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hfit : (fromByteArrayBigEndian (ret2.extract 0 32)) *
      (fromByteArrayBigEndian (ret1.extract 0 32)) < UInt256.size) :
    ExecStmt config
      { contract := contract,
        locals := amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm
      (.letDecl "balanceProduct" (some uint256)
        (checkedMul (.var "initialBalance0") (.var "initialBalance1")))
      (.ok ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm) := by
  simpa [amm4CtorAfterProductLocals] using
    (ExecStmt.letDecl (amm4CtorEvalInitialProductOk t0 t1 liquidity ret1 ret2 evm hfit))

theorem amm4CtorProductStmtOverflow
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32))) :
    ExecStmt config
      { contract := contract,
        locals := amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 }
      evm
      (.letDecl "balanceProduct" (some uint256)
        (checkedMul (.var "initialBalance0") (.var "initialBalance1")))
      .reverted := by
  exact ExecStmt.letDeclRevert
    (amm4CtorEvalInitialProductOverflow t0 t1 liquidity ret1 ret2 evm hover)

theorem amm4CtorEvalLiquidityAfterProduct
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm (.var "liquidity") = .ok (.int liquidity) := by
  simp only [evalExpr?, amm4CtorAfterProductLocals,
    amm4CtorAfterInitialBalance0Locals,
    amm4CtorAfterInitialBalance1Locals,
    amm4CtorAfterBaseLocals]
  rw [store_get_ne _ (k := "balanceProduct") (a := "liquidity") _ (by decide)]
  rw [store_get_ne _ (k := "initialBalance0") (a := "liquidity") _ (by decide)]
  rw [store_get_ne _ (k := "initialBalance1") (a := "liquidity") _ (by decide)]
  rw [store_get_ne _ (k := "baseSupply") (a := "liquidity") _ (by decide)]
  simpa only [evalExpr?] using amm4CtorEvalLiquidity t0 t1 liquidity evm

theorem amm4CtorEvalLiquiditySquareOk
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity)
    (hfit : liquidity.toNat * liquidity.toNat < UInt256.size) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm (checkedMul (.var "liquidity") (.var "liquidity")) =
      .ok (.int (Int.ofNat (liquidity.toNat * liquidity.toNat))) := by
  have hliq := amm4CtorEvalLiquidityAfterProduct t0 t1 liquidity ret1 ret2 evm
  have hval : (Value.int liquidity) = .int (Int.ofNat liquidity.toNat) :=
    congrArg Value.int (Int.toNat_of_nonneg h0).symm
  have hliqNat : evalExpr? config
      ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.var "liquidity") = .ok (.int (Int.ofNat liquidity.toNat)) := by
    rw [hval] at hliq
    exact hliq
  exact amm4EvalCheckedMul_ok (cfg := config)
    (frame := ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (x := .var "liquidity") (y := .var "liquidity")
    (a := liquidity.toNat) (b := liquidity.toNat) hliqNat hliqNat hfit

theorem amm4CtorEvalLiquiditySquareOverflow
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity)
    (hover : UInt256.size ≤ liquidity.toNat * liquidity.toNat) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm (checkedMul (.var "liquidity") (.var "liquidity")) = .revert := by
  have hliq := amm4CtorEvalLiquidityAfterProduct t0 t1 liquidity ret1 ret2 evm
  have hval : (Value.int liquidity) = .int (Int.ofNat liquidity.toNat) :=
    congrArg Value.int (Int.toNat_of_nonneg h0).symm
  have hliqNat : evalExpr? config
      ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.var "liquidity") = .ok (.int (Int.ofNat liquidity.toNat)) := by
    rw [hval] at hliq
    exact hliq
  exact amm4EvalCheckedMul_revert (cfg := config)
    (frame := ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (x := .var "liquidity") (y := .var "liquidity")
    (a := liquidity.toNat) (b := liquidity.toNat) hliqNat hliqNat hover

def amm4CtorAfterSquareLocals
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) : Store :=
  (amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2).insert
    "liquiditySquared" (.int (Int.ofNat (liquidity.toNat * liquidity.toNat)))

theorem amm4CtorSquareStmtOk
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity)
    (hfit : liquidity.toNat * liquidity.toNat < UInt256.size) :
    ExecStmt config
      { contract := contract,
        locals := amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm
      (.letDecl "liquiditySquared" (some uint256)
        (checkedMul (.var "liquidity") (.var "liquidity")))
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm) := by
  simpa [amm4CtorAfterSquareLocals] using
    (ExecStmt.letDecl
      (amm4CtorEvalLiquiditySquareOk t0 t1 liquidity ret1 ret2 evm h0 hfit))

theorem amm4CtorSquareStmtOverflow
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity)
    (hover : UInt256.size ≤ liquidity.toNat * liquidity.toNat) :
    ExecStmt config
      { contract := contract,
        locals := amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2 }
      evm
      (.letDecl "liquiditySquared" (some uint256)
        (checkedMul (.var "liquidity") (.var "liquidity")))
      .reverted := by
  exact ExecStmt.letDeclRevert
    (amm4CtorEvalLiquiditySquareOverflow t0 t1 liquidity ret1 ret2 evm h0 hover)

theorem amm4SolmCtorExecReverts_productOverflow
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
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"])
      (.ok ⟨contract, amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        (.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))) :: _)
      .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert
        (amm4CtorProductStmtOverflow t0 t1 liquidity ret1 ret2 evm2 hover))

theorem amm4CtorSourceProductSuccess
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
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"])
      (.ok ⟨contract, amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))])
      (.ok ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
  have htail : ExecBlock config
      ⟨contract, amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2⟩
      evm2 [.letDecl "balanceProduct" (some uint256)
        (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]
      (.ok ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
    simpa only [collapseReturns] using
      (ExecBlock.consNormal
        (amm4CtorProductStmtOk t0 t1 liquidity ret1 ret2 evm2 hfit)
        ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem amm4SolmCtorExecReverts_squareOverflow
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
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))])
      (.ok ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm ((((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        (.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))) :: _)
      .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert
        (amm4CtorSquareStmtOverflow t0 t1 liquidity ret1 ret2 evm2 h0 hover))

theorem amm4CtorSourceSquareSuccess
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
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))])
      (.ok ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))]))
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
  have htail : ExecBlock config
      ⟨contract, amm4CtorAfterProductLocals t0 t1 liquidity ret1 ret2⟩
      evm2 [.letDecl "liquiditySquared" (some uint256)
        (checkedMul (.var "liquidity") (.var "liquidity"))]
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
    simpa only [collapseReturns] using
      (ExecBlock.consNormal
        (amm4CtorSquareStmtOk t0 t1 liquidity ret1 ret2 evm2 h0 hfit)
        ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem amm4CtorEvalProductLocal
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.var "balanceProduct") =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (ret2.extract 0 32)) *
          (fromByteArrayBigEndian (ret1.extract 0 32))))) := by
  simp only [evalExpr?, amm4CtorAfterSquareLocals]
  rw [store_get_ne _ (k := "liquiditySquared") (a := "balanceProduct") _ (by decide)]
  simp only [amm4CtorAfterProductLocals, store_get_self, EvalResult.ofOption]

theorem amm4CtorEvalSquareLocal
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.var "liquiditySquared") =
      .ok (.int (Int.ofNat (liquidity.toNat * liquidity.toNat))) := by
  simp only [evalExpr?, amm4CtorAfterSquareLocals, store_get_self,
    EvalResult.ofOption]

theorem amm4CtorEvalProductEqTrue
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (heq : liquidity.toNat * liquidity.toNat =
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32))) :
    evalExpr? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")) =
      .ok (.bool true) := by
  simp only [evalExpr?, amm4CtorEvalSquareLocal,
    amm4CtorEvalProductLocal, EvalResult.bind, bind, evalBinaryOp?]
  rw [heq]
  simp

theorem amm4CtorEvalProductEqFalse
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hne : liquidity.toNat * liquidity.toNat ≠
      (fromByteArrayBigEndian (ret2.extract 0 32)) *
        (fromByteArrayBigEndian (ret1.extract 0 32))) :
    evalExpr? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
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
  simp only [evalExpr?, amm4CtorEvalSquareLocal,
    amm4CtorEvalProductLocal, EvalResult.bind, bind, evalBinaryOp?]
  rw [beq_false_of_ne hneValue]

theorem amm4SolmCtorExecReverts_productMismatch
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
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))]))
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm ((((((amm4CtorSourceStoredPrefix ++
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
        (amm4CtorEvalProductEqFalse t0 t1 liquidity ret1 ret2 evm2 hne)))

theorem amm4CtorEvalLiquidityAfterSquare
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.var "liquidity") = .ok (.int liquidity) := by
  simp only [evalExpr?, amm4CtorAfterSquareLocals]
  rw [store_get_ne _ (k := "liquiditySquared") (a := "liquidity") _ (by decide)]
  simpa only [evalExpr?] using
    amm4CtorEvalLiquidityAfterProduct t0 t1 liquidity ret1 ret2 evm

theorem amm4CtorEvalPositiveAfterSquare
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (hpos : 0 < liquidity) :
    evalExpr? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.binary .gt (.var "liquidity") (.intLit 0)) =
      .ok (.bool true) := by
  simp only [evalExpr?, amm4CtorEvalLiquidityAfterSquare,
    EvalResult.bind, bind, evalBinaryOp?]
  simp [hpos]

theorem amm4CtorSourceGuardsSuccess
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
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))]))
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((((((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))])) ++
        [.require (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")),
         .require (.binary .gt (.var "liquidity") (.intLit 0))])
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
  have htail : ExecBlock config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2
      [.require (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")),
       .require (.binary .gt (.var "liquidity") (.intLit 0))]
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2) := by
    apply ExecBlock.consNormal
      (ExecStmt.requireTrue
        (amm4CtorEvalProductEqTrue t0 t1 liquidity ret1 ret2 evm2 heq))
    apply ExecBlock.consNormal
      (ExecStmt.requireTrue
        (amm4CtorEvalPositiveAfterSquare t0 t1 liquidity ret1 ret2 evm2 hpos))
    exact ExecBlock.nil
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm4
