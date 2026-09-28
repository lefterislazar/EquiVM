import Benchmarks.ActAmm.ConstructorArgsTrace
import Benchmarks.ActAmm.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

theorem ammCtorReachBaseSupplyRoutine
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = ammCtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1526⟩ [liquidity, ⟨1000⟩, ⟨63⟩,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd49⟩ := ammCtorReachBody
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd1526 := amm_ctor_run rd49 with [
    jumpdest, push2 ⟨1000⟩, dup2, push2 ⟨63⟩, swap2, swap1,
    push2 ⟨1526⟩, jump (by amm_ctor_jd)]
  exact ⟨_, _, by simpa using rd1526⟩

theorem ammCtorReachBaseSubCheck
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = ammCtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1559⟩ [UInt256.isZero (UInt256.gt (UInt256.sub liquidity ⟨1000⟩) liquidity),
        UInt256.sub liquidity ⟨1000⟩, liquidity, ⟨1000⟩, ⟨63⟩,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1526⟩ := ammCtorReachBaseSupplyRoutine
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd1350a := amm_ctor_run rd1526 with [
    jumpdest, push0, push2 ⟨1536⟩, dup3, push2 ⟨1350⟩,
    jump (by amm_ctor_jd)]
  have rd1536 := amm_ctor_run rd1350a with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump (by amm_ctor_jd)]
  have rd1350b := amm_ctor_run rd1536 with [
    jumpdest, swap2, pop, push2 ⟨1547⟩, dup4,
    push2 ⟨1350⟩, jump (by amm_ctor_jd)]
  have rd1547 := amm_ctor_run rd1350b with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump (by amm_ctor_jd)]
  have rd1559 := amm_ctor_run rd1547 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop,
    dup2, dup2, gt, iszero]
  exact ⟨_, _, by simpa using rd1559⟩

theorem ammCtorBaseSubUnderflowGt (liquidity : UInt256)
    (hunder : liquidity.toNat < 1000) :
    UInt256.gt (UInt256.sub liquidity ⟨1000⟩) liquidity = ⟨1⟩ := by
  have hsubNat : (UInt256.sub liquidity ⟨1000⟩).toNat =
      UInt256.size + liquidity.toNat - (⟨1000⟩ : UInt256).toNat :=
    usub_toNat_underflow (by simpa using hunder)
  show UInt256.fromBool (decide (UInt256.sub liquidity ⟨1000⟩ > liquidity)) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show (UInt256.sub liquidity ⟨1000⟩).toNat > liquidity.toNat
    rw [hsubNat]
    have h1000 : (⟨1000⟩ : UInt256).toNat = 1000 := by decide
    rw [h1000]
    have hsize : UInt256.size = 2 ^ 256 := rfl
    omega

theorem ammCtorBaseSubNoUnderflowGt (liquidity : UInt256)
    (hle : 1000 ≤ liquidity.toNat) :
    UInt256.gt (UInt256.sub liquidity ⟨1000⟩) liquidity = ⟨0⟩ := by
  have hsubNat : (UInt256.sub liquidity ⟨1000⟩).toNat =
      liquidity.toNat - (⟨1000⟩ : UInt256).toNat :=
    usub_toNat (by simpa using hle)
  show UInt256.fromBool (decide (UInt256.sub liquidity ⟨1000⟩ > liquidity)) = ⟨0⟩
  have hnot : ¬ UInt256.sub liquidity ⟨1000⟩ > liquidity := by
    change ¬ (UInt256.sub liquidity ⟨1000⟩).toNat > liquidity.toNat
    rw [hsubNat]
    omega
  simp [hnot]
  rfl

theorem ammCtorReachBaseUnderflowPanic
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = ammCtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hunder : liquidity.toNat < 1000) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1481⟩ [⟨1570⟩, UInt256.sub liquidity ⟨1000⟩,
        liquidity, ⟨1000⟩, ⟨63⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1559⟩ := ammCtorReachBaseSubCheck
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  rw [ammCtorBaseSubUnderflowGt liquidity hunder] at rd1559
  have rd1481 := amm_ctor_run rd1559 with [
    push2 ⟨1571⟩, jumpiNT (by decide),
    push2 ⟨1570⟩, push2 ⟨1481⟩, jump (by amm_ctor_jd)]
  exact ⟨_, _, by simpa using rd1481⟩

theorem ammCtorBaseUnderflowRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = ammCtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hunder : liquidity.toNat < 1000) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  obtain ⟨_, _, rd1481⟩ := ammCtorReachBaseUnderflowPanic
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hunder
  let mem := ammCtorDecodedMem t0 t1 liquidity
  have rd1482 := amm_ctor_run rd1481 with [jumpdest]
  have rd1515 := rd1482.pushConst ammPanicSelector
    (width := 32) (op := .PUSH32) (by decide) (by amm_ctor_decode) (by evm_ov)
  have rd1516 := amm_ctor_run rd1515 with [push0]
  have rd1517 := rd1516.mstore 0 (ammPanicMem0 mem) (UInt256.ofNat 7)
    (by amm_ctor_decode) mem_cost (by rfl) (by native_decide) (by simp)
  have rd1522 := amm_ctor_run rd1517 with [push1 ⟨17⟩, push1 ⟨4⟩]
  have rd1523 := rd1522.mstore 0 (ammPanicMem mem) (UInt256.ofNat 7)
    (by amm_ctor_decode) mem_cost (by rfl) (by native_decide) (by simp)
  have rd1525 := amm_ctor_run rd1523 with [push1 ⟨36⟩, push0]
  exact rd1525.rev 0 (by amm_ctor_decode) mem_cost (by evm_ov)

theorem ammCtorReachBaseSupplyOk
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = ammCtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hle : 1000 ≤ liquidity.toNat) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨63⟩ [UInt256.sub liquidity ⟨1000⟩, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1559⟩ := ammCtorReachBaseSubCheck
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  rw [ammCtorBaseSubNoUnderflowGt liquidity hle] at rd1559
  have rd1571 := amm_ctor_run rd1559 with [
    push2 ⟨1571⟩, jumpiT (by decide) (by amm_ctor_jd)]
  have rd63 := amm_ctor_run rd1571 with [
    jumpdest, swap3, swap2, pop, pop, jump (by amm_ctor_jd)]
  exact ⟨_, _, by simpa using rd63⟩

theorem ammCtorReachBaseSupplyStored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = ammCtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : 1000 ≤ liquidity.toNat) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨70⟩ [UInt256.sub liquidity ⟨1000⟩, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σ ⟨0⟩
          (UInt256.sub liquidity ⟨1000⟩)) k C := by
  obtain ⟨_, _, rd63⟩ := ammCtorReachBaseSupplyOk
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hle
  have rd68 := amm_ctor_run rd63 with [jumpdest, dup1, push0, dup2, swap1]
  obtain ⟨_, _, rd69⟩ := rd68.sstore hperm (by amm_ctor_decode) (by simp)
  have rd70 := amm_ctor_run rd69 with [pop]
  exact ⟨_, _, by simpa using rd70⟩

end Benchmarks.ActAmm
