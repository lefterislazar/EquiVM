import Benchmarks.ActAmm4.ConstructorCallReady
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def amm4CtorInitialToken1PostCallMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) (ret : ByteArray) : ByteArray :=
  ret.write 0 (amm4CtorInitialToken1ArgMem I t0 t1 liquidity) 224
    (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat

theorem amm4CtorFirstStaticcall
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : 1000 ≤ liquidity.toNat)
    (hne : t0 ≠ t1)
    (hdepth : I.depth.val < 1024) :
    ∃ (createdAccounts' : Batteries.RBSet AccountAddress compare)
      (σ' : AccountMap) (z : Bool) (ret : ByteArray)
      (A' : Substate) (k C : Nat),
      RD (amm4CtorCode t0 t1 liquidity) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        ⟨422⟩ ((if z then ⟨1⟩ else ⟨0⟩) ::
          [⟨260⟩, ⟨1889567281⟩,
            amm4CtorInitialToken1Target I σ liquidity t0 t1,
            liquidity, EVM.word t1, EVM.word t0])
        (amm4CtorInitialToken1PostCallMem I t0 t1 liquidity ret)
        (UInt256.ofNat 9) ret (createdAccounts', σ') k C ∧
      typedCallViaEVM config
        { initState createdAccounts genesisBlockHeader blocks
            (amm4CtorToken1Storage I σ liquidity t0 t1) σ₀ g A I with
          accountMap := amm4CtorToken1Storage I σ liquidity t0 t1 }
        (AccountAddress.ofUInt256
          (amm4CtorInitialToken1Target I σ liquidity t0 t1))
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState createdAccounts genesisBlockHeader blocks
            (amm4CtorToken1Storage I σ liquidity t0 t1) σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := createdAccounts' }, ret)
        false ∧ ret.size < UInt256.size ∧ ret.size < 2 ^ 138 := by
  obtain ⟨gasWord, _, _, rd421⟩ := amm4CtorReachInitialToken1Staticcall
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  obtain ⟨createdAccounts', σ', z, ret, A_in, callGas, k, C, hΘpack,
    rd422, hretsz⟩ :=
    RD.solcStaticcall rd421 (by amm4_ctor_decode) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M 9 224 36) 224 32) = ⟨9⟩ := by native_decide
  refine ⟨createdAccounts', σ', z, ret, A', k, C, ?_, ?_, hretsz, ?_⟩
  · simpa only [haw, amm4CtorInitialToken1PostCallMem] using rd422
  · refine callCoincides (A_in := A_in) (g'' := g'')
      (callGas := callGas) (callPerm := false)
      (targetWord := amm4CtorInitialToken1Target I σ liquidity t0 t1)
      (mem := amm4CtorInitialToken1ArgMem I t0 t1 liquidity)
      (inOff := ⟨224⟩) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by
        rw [show I.depth = (1024 : Fin 1025) from h]
        decide))
      rfl (amm4CtorInitialToken1ArgMem_encode I t0 t1 liquidity) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((amm4CtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 224 36).size =
          36 := by
      rw [amm4CtorInitialToken1ArgMem_read36, ByteArray.size_append,
        toByteArray_size]
      decide
    have hinputBound :
        ((amm4CtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 224 36).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes createdAccounts genesisBlockHeader blocks
      (amm4CtorToken1Storage I σ liquidity t0 t1) σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256
        (amm4CtorInitialToken1Target I σ liquidity t0 t1))
      (toExecute (amm4CtorToken1Storage I σ liquidity t0 t1)
        (AccountAddress.ofUInt256
          (amm4CtorInitialToken1Target I σ liquidity t0 t1)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((amm4CtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 224 36)
      (I.depth + 1) I.header false
      (by simpa [initState] using hΘ) hinputBound

theorem amm4CtorFirstCallFailed
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
      ⟨422⟩ (⟨0⟩ :: R) mem aw ret acc k C)
    (hretsz : ret.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev (amm4CtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd429 := amm4_ctor_run rd with [
    iszero, dup1, iszero, push2 ⟨436⟩, jumpiNT (by decide)]
  have rd432 := amm4_ctor_run rd429 with [returndatasize, push0, push0]
  let len := UInt256.ofNat ret.size
  let memout := ret.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd433 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd432 (by amm4_ctor_decode)
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
  have rd435 := amm4_ctor_run rd433 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd435 (by amm4_ctor_decode)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

end Benchmarks.ActAmm4
