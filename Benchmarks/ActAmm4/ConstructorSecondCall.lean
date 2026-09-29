import Benchmarks.ActAmm4.ConstructorSecondCallTrace
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def amm4CtorSecondCallPostCallMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) : ByteArray :=
  ret2.write 0 (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1)
    (amm4CtorSecondCallFreePtr ret1).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat ret2.size)).toNat

theorem amm4CtorSecondStaticcall
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap}
    {A Apre : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 gasWord : UInt256}
    {ret1 : ByteArray}
    {k C : Nat}
    (hlo : 32 ≤ ret1.size) (hbound : ret1.size < 2 ^ 138)
    (hdepth : I.depth.val < 1024)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨574⟩ (gasWord ::
        [amm4CtorInitialToken0Target I σ,
          amm4CtorSecondCallFreePtr ret1, ⟨36⟩,
          amm4CtorSecondCallFreePtr ret1, ⟨32⟩,
          amm4CtorSecondCallFreePtr ret1 + ⟨36⟩,
          ⟨1889567281⟩, amm4CtorInitialToken0Target I σ,
          v1, liquidity, EVM.word t1, EVM.word t0])
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1)
      (amm4CtorSecondCallArgWords ret1) ret1 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (ret2 : ByteArray) (A' : Substate) (k' C' : Nat),
      RD (amm4CtorCode t0 t1 liquidity) I g
        (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
        ⟨575⟩ ((if z then ⟨1⟩ else ⟨0⟩) ::
          [amm4CtorSecondCallFreePtr ret1 + ⟨36⟩,
            ⟨1889567281⟩, amm4CtorInitialToken0Target I σ,
            v1, liquidity, EVM.word t1, EVM.word t0])
        (amm4CtorSecondCallPostCallMem I t0 t1 liquidity ret1 ret2)
        (amm4CtorSecondCallArgWords ret1) ret2 (cA', σ') k' C' ∧
      typedCallViaEVM config
        (initState cA genesisBlockHeader blocks σ σ₀ g Apre I)
        (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ))
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState cA genesisBlockHeader blocks σ σ₀ g Apre I with
          accountMap := σ', substate := A', createdAccounts := cA' }, ret2) false ∧
      ret2.size < UInt256.size ∧ ret2.size < 2 ^ 138 := by
  obtain ⟨cA', σ', z, ret2, A_in, callGas, k', C', hΘpack,
    rd575, hretsz⟩ :=
    RD.solcStaticcall rd (by amm4_ctor_decode) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M
        (MachineState.M (amm4CtorSecondCallArgWords ret1).toNat
          (amm4CtorSecondCallFreePtr ret1).toNat (⟨36⟩ : UInt256).toNat)
        (amm4CtorSecondCallFreePtr ret1).toNat (⟨32⟩ : UInt256).toNat) =
      amm4CtorSecondCallArgWords ret1 := by
    rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      amm4CtorSecondCallArgWords_callInput_nat_same ret1 hlo hbound]
    exact amm4CtorSecondCallArgWords_call_same ret1 hlo hbound
  refine ⟨cA', σ', z, ret2, A', k', C', ?_, ?_, hretsz, ?_⟩
  · simpa only [haw, amm4CtorSecondCallPostCallMem] using rd575
  · refine callCoincides (A_in := A_in) (g'' := g'')
      (callGas := callGas) (callPerm := false)
      (targetWord := amm4CtorInitialToken0Target I σ)
      (mem := amm4CtorSecondCallArgMem I t0 t1 liquidity ret1)
      (inOff := amm4CtorSecondCallFreePtr ret1) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by
        rw [show I.depth = (1024 : Fin 1025) from h]
        decide))
      rfl (amm4CtorSecondCallArgMem_encode I t0 t1 liquidity ret1 hbound) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((amm4CtorSecondCallArgMem I t0 t1 liquidity ret1).readWithPadding
          (amm4CtorSecondCallFreePtr ret1).toNat 36).size = 36 := by
      rw [amm4CtorSecondCallArgMem_read36 I t0 t1 liquidity ret1 hbound,
        ByteArray.size_append, toByteArray_size]
      decide
    have hinputBound :
        ((amm4CtorSecondCallArgMem I t0 t1 liquidity ret1).readWithPadding
          (amm4CtorSecondCallFreePtr ret1).toNat 36).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA genesisBlockHeader blocks σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ))
      (toExecute σ (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((amm4CtorSecondCallArgMem I t0 t1 liquidity ret1).readWithPadding
        (amm4CtorSecondCallFreePtr ret1).toNat 36)
      (I.depth + 1) I.header false
      (by simpa [initState] using hΘ) hinputBound

theorem amm4CtorSecondCallFailed
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {mem ret : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨575⟩ (⟨0⟩ :: R) mem aw ret acc k C)
    (hretsz : ret.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev (amm4CtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd582 := amm4_ctor_run rd with [
    iszero, dup1, iszero, push2 ⟨589⟩, jumpiNT (by decide)]
  have rd585 := amm4_ctor_run rd582 with [returndatasize, push0, push0]
  let len := UInt256.ofNat ret.size
  let memout := ret.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd586 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd585 (by amm4_ctor_decode)
    (by
      change 0 + len.toNat ≤ ret.size
      dsimp [len]
      rw [ulit_toNat' ret.size hretsz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd588 := amm4_ctor_run rd586 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd588 (by amm4_ctor_decode)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

end Benchmarks.ActAmm4
