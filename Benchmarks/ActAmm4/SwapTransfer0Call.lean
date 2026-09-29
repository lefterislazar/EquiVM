import Benchmarks.ActAmm4.SwapTransfer0Trace
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_transfer0Call
    {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hto : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hframe : ∃ (gasWord : UInt256) (k C : Nat), RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2606⟩
      [gasWord, amm4MintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0CalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A' : Substate) (k' C' : Nat),
      RD amm4Bytecode I g
        (initState cAstart gh bl σstart σ₀ g A I) ⟨2607⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨3077966991⟩ ::
          amm4MintToken0Word σ I :: amm4SwapToWord I ::
          amm4SwapAmount1Word I :: amm4SwapAmount0Word I :: ⟨349⟩ :: [sel])
        (o.write 0 (amm4SwapTransfer0CalldataMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 7) o (cA', σ') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with accountMap := σ }
        (AccountAddress.ofUInt256 (amm4MintToken0Word σ I))
        "transfer" 0
        [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
          .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
        (z, { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o)
        true ∧
      o.size < UInt256.size ∧ o.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd1222⟩ := hframe
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘpack, rd1223, hosz⟩ :=
    RD.call rd1222 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat 128 68)
        128 32) = UInt256.ofNat 7 := by native_decide
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz, ?_⟩
  · simpa [haw] using rd1223
  · refine callCoincides (A_in := A_in) (g'' := g'')
      (callGas := callGas) (callPerm := true)
      (targetWord := amm4MintToken0Word σ I)
      (mem := amm4SwapTransfer0CalldataMem I)
      (inOff := ⟨128⟩) (inSize := ⟨68⟩)
      (fun h => absurd hdepth
        (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl (amm4SwapTransfer0CalldataMem_encode I hto) ?_
    simpa [initState, hperm] using hΘ
  · have hinputSize :
        ((amm4SwapTransfer0CalldataMem I).readWithPadding 128 68).size =
          68 := by
      rw [readWithPadding_eq_extract' _ 128 68
        (by norm_num) (by norm_num)
        (by rw [amm4SwapTransfer0CalldataMem_size])]
      rw [ByteArray.size_extract, amm4SwapTransfer0CalldataMem_size]
      omega
    have hbound :
        ((amm4SwapTransfer0CalldataMem I).readWithPadding 128 68).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA gh bl σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (amm4MintToken0Word σ I))
      (toExecute σ (AccountAddress.ofUInt256 (amm4MintToken0Word σ I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((amm4SwapTransfer0CalldataMem I).readWithPadding 128 68)
      (I.depth + 1) I.header true
      (by simpa [initState, hperm] using hΘ) hbound

theorem amm4SwapX_transfer0CallFailed
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨2607⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1230 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨2621⟩, jumpiNT (by decide)]
  have rd1233 := evm_run rd1230 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd1234 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd1233 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [ulit_toNat' o.size hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd1236 := evm_run rd1234 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) -
      Cₘ awout)
    rd1236 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem amm4SwapX_transfer0DepthRevert
    {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : Nat}
    (hdepth : I.depth = 1024)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2606⟩
      [gasWord, amm4MintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0CalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  obtain ⟨_, _, rd1223⟩ := RD.callDepthLimit rd
    (by native_decide) hdepth
    (by simp only [List.length_cons, List.length_nil]; omega)
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat 128 68)
        128 32) = UInt256.ofNat 7 := by native_decide
  have rd1223' := rd1223
  simpa [haw, byteArray_write_len_zero] using
    (amm4SwapX_transfer0CallFailed rd1223'
      (by decide)
      (by simp only [List.length_cons, List.length_nil]; omega))

theorem amm4SwapX_transfer0CallSucceeded
    {cAstart gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2607⟩
      [⟨1⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      mem aw o acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2626⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨2621⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

end Benchmarks.ActAmm4
