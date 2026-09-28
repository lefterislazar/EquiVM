import Benchmarks.ActAmm.ConstructorSecondCallDecode
import Benchmarks.ActAmm.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem RD.ammCtorCleanupUint
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {a ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1350⟩ (a :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ret (a :: R) mem aw rdata acc k' C' := by
  have hlen1 : (ret :: R).length = R.length + 1 := by simp
  have hlen2 : (a :: ret :: R).length = R.length + 2 := by simp
  have rd1358 := amm_ctor_run h with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop]
  exact ⟨_, _, rd1358.jump (by amm_ctor_decode) hret (by evm_ov)⟩

theorem RD.ammCtorCheckedMulToCondition
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1660⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1706⟩
      (UInt256.lor (UInt256.isZero a)
        (UInt256.eq b (UInt256.div (UInt256.mul a b) a)) ::
       UInt256.mul a b :: UInt256.mul a b :: a :: b :: ret :: R)
      mem aw rdata acc k' C' := by
  have hlen0 : ((⟨0⟩ : UInt256) :: a :: b :: ret :: R).length =
      R.length + 4 := by simp
  have hlen1 : (UInt256.mul a b :: (⟨0⟩ : UInt256) :: a :: b :: ret :: R).length =
      R.length + 5 := by simp
  have rd1670₀ := amm_ctor_run h with [
    jumpdest, push0, push2 ⟨1670⟩, dup3, push2 ⟨1350⟩,
    jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1670⟩ := RD.ammCtorCleanupUint rd1670₀
    (by amm_ctor_jd) (by omega)
  have rd1681₀ := amm_ctor_run rd1670 with [
    jumpdest, swap2, pop, push2 ⟨1681⟩, dup4, push2 ⟨1350⟩,
    jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1681⟩ := RD.ammCtorCleanupUint rd1681₀
    (by amm_ctor_jd) (by omega)
  have rd1695₀ := amm_ctor_run rd1681 with [
    jumpdest, swap3, pop, dup3, dup3, mul, push2 ⟨1695⟩,
    dup2, push2 ⟨1350⟩, jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1695⟩ := RD.ammCtorCleanupUint rd1695₀
    (by amm_ctor_jd) (by omega)
  exact ⟨_, _, amm_ctor_run rd1695 with [
    jumpdest, swap2, pop, dup3, dup3, div, dup5, eq, dup4, iszero, or]⟩

theorem RD.ammCtorCheckedMulOk
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1660⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hfit : a.toNat * b.toNat < UInt256.size)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ret (UInt256.mul a b :: R) mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd1706₀⟩ := RD.ammCtorCheckedMulToCondition h hov
  have rd1706 := rd1706₀
  rw [ammCheckedMulConditionOk a b hfit] at rd1706
  have rd1718 := amm_ctor_run rd1706 with [
    push2 ⟨1718⟩, jumpiT (by decide) (by amm_ctor_jd)]
  exact ⟨_, _, amm_ctor_run rd1718 with [
    jumpdest, pop, swap3, swap2, pop, pop, jump hret]⟩

theorem RD.ammCtorPanicOverflowRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1481⟩ R mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat) (hov : R.length + 2 ≤ 1024) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have hM0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
    change UInt256.ofNat (max aw.toNat 1) = aw
    rw [max_eq_left (by omega : 1 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hM4 : UInt256.ofNat (MachineState.M aw.toNat 4 32) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hMrev : UInt256.ofNat (MachineState.M aw.toNat 0 36) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have rd1482 := amm_ctor_run h with [jumpdest]
  have rd1515 := rd1482.pushConst ammPanicSelector
    (width := 32) (op := .PUSH32) (by decide) (by amm_ctor_decode) (by evm_ov)
  have rd1522 := amm_ctor_run rd1515 with [
    push0,
    raw mstore 0 (ammPanicMem0 mem) aw
      (by amm_ctor_decode) (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hM0, Nat.sub_self])
      (by rfl) (by simpa using hM0) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩,
    raw mstore 0 (ammPanicMem mem) aw
      (by amm_ctor_decode) (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        simp only [show (⟨4⟩ : UInt256).toNat = 4 from rfl, hM4, Nat.sub_self])
      (by rfl) (by simpa using hM4) (by evm_ov)]
  have rd1525 := amm_ctor_run rd1522 with [push1 ⟨36⟩, push0]
  exact rd1525.rev 0 (by amm_ctor_decode) (by
    intro s hs hst
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (⟨36⟩ : UInt256).toNat = 36 from rfl,
      hMrev, Nat.sub_self]) (by evm_ov)

theorem RD.ammCtorCheckedMulOverflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1660⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat)
    (haw : 3 ≤ aw.toNat) (hov : R.length + 12 ≤ 1024) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  obtain ⟨_, _, rd1706₀⟩ := RD.ammCtorCheckedMulToCondition h hov
  have rd1706 := rd1706₀
  rw [ammCheckedMulConditionOverflow a b hover] at rd1706
  have rd1481 := amm_ctor_run rd1706 with [
    push2 ⟨1718⟩, jumpiNT (by decide),
    push2 ⟨1717⟩, push2 ⟨1481⟩, jump (by amm_ctor_jd)]
  exact RD.ammCtorPanicOverflowRevert rd1481 haw
    (by simp only [List.length_cons]; omega)

theorem ammCtorInitialProductOk
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity v0 v1 : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨625⟩ [v0, v1, liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hfit : v0.toNat * v1.toNat < UInt256.size) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨635⟩ [UInt256.mul v0 v1, liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k' C' := by
  have rd1660 := amm_ctor_run rd with [
    jumpdest, push2 ⟨635⟩, swap2, swap1, push2 ⟨1660⟩,
    jump (by amm_ctor_jd)]
  exact RD.ammCtorCheckedMulOk rd1660 hfit
    (by amm_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)

theorem ammCtorInitialProductOverflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity v0 v1 : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨625⟩ [v0, v1, liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hover : UInt256.size ≤ v0.toNat * v1.toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd1660 := amm_ctor_run rd with [
    jumpdest, push2 ⟨635⟩, swap2, swap1, push2 ⟨1660⟩,
    jump (by amm_ctor_jd)]
  exact RD.ammCtorCheckedMulOverflow rd1660 hover haw
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ammCtorLiquiditySquareOk
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity product : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨635⟩ [product, liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hfit : liquidity.toNat * liquidity.toNat < UInt256.size) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨647⟩ [UInt256.mul liquidity liquidity, product, liquidity,
        EVM.word t1, EVM.word t0]
      mem aw rdata acc k' C' := by
  have rd1660 := amm_ctor_run rd with [
    jumpdest, dup2, dup3, push2 ⟨647⟩, swap2, swap1,
    push2 ⟨1660⟩, jump (by amm_ctor_jd)]
  exact RD.ammCtorCheckedMulOk rd1660 hfit
    (by amm_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)

theorem ammCtorLiquiditySquareOverflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity product : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨635⟩ [product, liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hover : UInt256.size ≤ liquidity.toNat * liquidity.toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd1660 := amm_ctor_run rd with [
    jumpdest, dup2, dup3, push2 ⟨647⟩, swap2, swap1,
    push2 ⟨1660⟩, jump (by amm_ctor_jd)]
  exact RD.ammCtorCheckedMulOverflow rd1660 hover haw
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ammCtorProductEqualityOk
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity product square : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨647⟩ [square, product, liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (heq : square = product) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨711⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k' C' := by
  subst square
  have rd650 := amm_ctor_run rd with [jumpdest, eq]
  have hcmp : UInt256.eq product product = ⟨1⟩ := u256_eq_refl product
  rw [hcmp] at rd650
  exact ⟨_, _, amm_ctor_run rd650 with [
    push2 ⟨711⟩, jumpiT (by decide) (by amm_ctor_jd)]⟩

theorem ammCtorPositiveLiquidityOk
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨711⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hpos : 0 < liquidity.toNat) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨777⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k' C' := by
  have rd715 := amm_ctor_run rd with [jumpdest, push0, dup2, gt]
  have hgt : UInt256.gt liquidity ⟨0⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa using hpos)
  rw [hgt] at rd715
  exact ⟨_, _, amm_ctor_run rd715 with [
    push2 ⟨777⟩, jumpiT (by decide) (by amm_ctor_jd)]⟩

end Benchmarks.ActAmm
