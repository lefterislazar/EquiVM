import Benchmarks.ActAmm.ConstructorFourthCallEncode
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def ammCtorFourthCallPostCallMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 ret4 : ByteArray) : ByteArray :=
  ret4.write 0 (ammCtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
    (ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat ret4.size)).toNat

theorem ammCtorFourthStaticcall
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A Apre : Substate}
    {I : ExecutionEnv} {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity gasWord : UInt256}
    {ret1 ret2 ret3 : ByteArray} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138)
    (hdepth : I.depth.val < 1024)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1191⟩ (gasWord ::
        [ammCtorFinalToken1Target I σ,
          ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3, ⟨36⟩,
          ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3, ⟨32⟩,
          ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨36⟩,
          ⟨1889567281⟩, ammCtorFinalToken1Target I σ,
          liquidity, EVM.word t1, EVM.word t0])
      (ammCtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorFourthCallArgWords ret1 ret2 ret3) ret3 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (ret4 : ByteArray) (A' : Substate) (k' C' : Nat),
      RD (ammCtorCode t0 t1 liquidity) I g
        (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
        ⟨1192⟩ ((if z then ⟨1⟩ else ⟨0⟩) ::
          [ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨36⟩,
            ⟨1889567281⟩, ammCtorFinalToken1Target I σ,
            liquidity, EVM.word t1, EVM.word t0])
        (ammCtorFourthCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
        (ammCtorFourthCallArgWords ret1 ret2 ret3) ret4 (cA', σ') k' C' ∧
      typedCallViaEVM config
        (initState cA genesisBlockHeader blocks σ σ₀ g Apre I)
        (AccountAddress.ofUInt256 (ammCtorFinalToken1Target I σ))
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState cA genesisBlockHeader blocks σ σ₀ g Apre I with
          accountMap := σ', substate := A', createdAccounts := cA' }, ret4) false ∧
      ret4.size < UInt256.size ∧ ret4.size < 2 ^ 138 := by
  obtain ⟨cA', σ', z, ret4, A_in, callGas, k', C', hΘpack,
    rd1192, hretsz⟩ :=
    RD.solcStaticcall rd (by amm_ctor_decode) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M
        (MachineState.M (ammCtorFourthCallArgWords ret1 ret2 ret3).toNat
          (ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat
          (⟨36⟩ : UInt256).toNat)
        (ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat
          (⟨32⟩ : UInt256).toNat) =
      ammCtorFourthCallArgWords ret1 ret2 ret3 := by
    rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      ammCtorFourthCallArgWords_call_nat_same ret1 ret2 ret3
        hlo1 hbound1 hlo2 hbound2 hlo3 hbound3 36 (Or.inr rfl),
      ammCtorFourthCallArgWords_call_nat_same ret1 ret2 ret3
        hlo1 hbound1 hlo2 hbound2 hlo3 hbound3 32 (Or.inl rfl)]
    exact u256_ofNat_toNat _
  refine ⟨cA', σ', z, ret4, A', k', C', ?_, ?_, hretsz, ?_⟩
  · simpa only [haw, ammCtorFourthCallPostCallMem] using rd1192
  · refine callCoincides (A_in := A_in) (g'' := g'')
      (callGas := callGas) (callPerm := false)
      (targetWord := ammCtorFinalToken1Target I σ)
      (mem := ammCtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
      (inOff := ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by
        rw [show I.depth = (1024 : Fin 1025) from h]
        decide))
      rfl (ammCtorFourthCallArgMem_encode I t0 t1 liquidity ret1 ret2 ret3
        hbound1 hbound2 hbound3) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((ammCtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
          (ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 36).size =
          36 := by
      rw [ammCtorFourthCallArgMem_read36 I t0 t1 liquidity ret1 ret2 ret3
        hbound1 hbound2 hbound3, ByteArray.size_append, toByteArray_size]
      decide
    have hinputBound :
        ((ammCtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
          (ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 36).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA genesisBlockHeader blocks σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (ammCtorFinalToken1Target I σ))
      (toExecute σ (AccountAddress.ofUInt256 (ammCtorFinalToken1Target I σ)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((ammCtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
        (ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 36)
      (I.depth + 1) I.header false
      (by simpa [initState] using hΘ) hinputBound

theorem ammCtorFourthCallFailed
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1192⟩ (⟨0⟩ :: R) mem aw ret acc k C)
    (hretsz : ret.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd1199 := amm_ctor_run rd with [
    iszero, dup1, iszero, push2 ⟨1206⟩, jumpiNT (by decide)]
  have rd1202 := amm_ctor_run rd1199 with [returndatasize, push0, push0]
  let len := UInt256.ofNat ret.size
  let memout := ret.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd1203 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd1202 (by amm_ctor_decode)
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
  have rd1205 := amm_ctor_run rd1203 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd1205 (by amm_ctor_decode)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

end Benchmarks.ActAmm
