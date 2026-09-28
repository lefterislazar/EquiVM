import Benchmarks.ActAmm.ConstructorThirdCallEncode
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def ammCtorThirdCallPostCallMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray) : ByteArray :=
  ret3.write 0 (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat ret3.size)).toNat

theorem ammCtorThirdStaticcall
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A Apre : Substate}
    {I : ExecutionEnv} {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity gasWord : UInt256}
    {ret1 ret2 : ByteArray} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hdepth : I.depth.val < 1024)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1032⟩ (gasWord ::
        [ammCtorInitialToken0Target I σ,
          ammCtorAfterSecondReturnFreePtr ret1 ret2, ⟨36⟩,
          ammCtorAfterSecondReturnFreePtr ret1 ret2, ⟨32⟩,
          ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩,
          ⟨1889567281⟩, ammCtorInitialToken0Target I σ,
          liquidity, EVM.word t1, EVM.word t0])
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (ammCtorThirdCallArgWords ret1 ret2) ret2 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (ret3 : ByteArray) (A' : Substate) (k' C' : Nat),
      RD (ammCtorCode t0 t1 liquidity) I g
        (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
        ⟨1033⟩ ((if z then ⟨1⟩ else ⟨0⟩) ::
          [ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩,
            ⟨1889567281⟩, ammCtorInitialToken0Target I σ,
            liquidity, EVM.word t1, EVM.word t0])
        (ammCtorThirdCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3)
        (ammCtorThirdCallArgWords ret1 ret2) ret3 (cA', σ') k' C' ∧
      typedCallViaEVM config
        (initState cA genesisBlockHeader blocks σ σ₀ g Apre I)
        (AccountAddress.ofUInt256 (ammCtorInitialToken0Target I σ))
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState cA genesisBlockHeader blocks σ σ₀ g Apre I with
          accountMap := σ', substate := A', createdAccounts := cA' }, ret3) false ∧
      ret3.size < UInt256.size ∧ ret3.size < 2 ^ 138 := by
  obtain ⟨cA', σ', z, ret3, A_in, callGas, k', C', hΘpack,
    rd1033, hretsz⟩ :=
    RD.solcStaticcall rd (by amm_ctor_decode) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M
        (MachineState.M (ammCtorThirdCallArgWords ret1 ret2).toNat
          (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat
          (⟨36⟩ : UInt256).toNat)
        (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat
          (⟨32⟩ : UInt256).toNat) =
      ammCtorThirdCallArgWords ret1 ret2 := by
    rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      ammCtorThirdCallArgWords_call_nat_same ret1 ret2
        hlo1 hbound1 hlo2 hbound2 36 (Or.inr rfl),
      ammCtorThirdCallArgWords_call_nat_same ret1 ret2
        hlo1 hbound1 hlo2 hbound2 32 (Or.inl rfl)]
    exact u256_ofNat_toNat _
  refine ⟨cA', σ', z, ret3, A', k', C', ?_, ?_, hretsz, ?_⟩
  · simpa only [haw, ammCtorThirdCallPostCallMem] using rd1033
  · refine callCoincides (A_in := A_in) (g'' := g'')
      (callGas := callGas) (callPerm := false)
      (targetWord := ammCtorInitialToken0Target I σ)
      (mem := ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (inOff := ammCtorAfterSecondReturnFreePtr ret1 ret2) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by
        rw [show I.depth = (1024 : Fin 1025) from h]
        decide))
      rfl (ammCtorThirdCallArgMem_encode I t0 t1 liquidity ret1 ret2
        hbound1 hbound2) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
          (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 36).size = 36 := by
      rw [ammCtorThirdCallArgMem_read36 I t0 t1 liquidity ret1 ret2
        hbound1 hbound2, ByteArray.size_append, toByteArray_size]
      decide
    have hinputBound :
        ((ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
          (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 36).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA genesisBlockHeader blocks σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (ammCtorInitialToken0Target I σ))
      (toExecute σ (AccountAddress.ofUInt256 (ammCtorInitialToken0Target I σ)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
        (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 36)
      (I.depth + 1) I.header false
      (by simpa [initState] using hΘ) hinputBound

theorem ammCtorThirdCallFailed
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1033⟩ (⟨0⟩ :: R) mem aw ret acc k C)
    (hretsz : ret.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd1040 := amm_ctor_run rd with [
    iszero, dup1, iszero, push2 ⟨1047⟩, jumpiNT (by decide)]
  have rd1043 := amm_ctor_run rd1040 with [returndatasize, push0, push0]
  let len := UInt256.ofNat ret.size
  let memout := ret.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd1044 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd1043 (by amm_ctor_decode)
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
  have rd1046 := amm_ctor_run rd1044 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd1046 (by amm_ctor_decode)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

end Benchmarks.ActAmm
