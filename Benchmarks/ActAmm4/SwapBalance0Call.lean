import Benchmarks.ActAmm4.SwapBalance0Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_balance0Staticcall
    {cAstart cA gh bl σstart σ σ₀ A Apre I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hdepth : I.depth.val < 1024)
    (hframe : ∃ (gasWord : UInt256) (k C : Nat), RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2918⟩
      [gasWord, amm4MintToken0Word σ I, amm4SwapBalance0FreePtr o0 o1,
        ⟨36⟩, amm4SwapBalance0FreePtr o0 o1, ⟨32⟩,
        amm4SwapBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken0Word σ I,
        ⟨0⟩, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
      (amm4SwapBalance0CalldataWords o0 o1)
      o1 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o2 : ByteArray) (A' : Substate) (k' C' : Nat),
      RD amm4Bytecode I g
        (initState cAstart gh bl σstart σ₀ g A I) ⟨2919⟩
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          (amm4SwapBalance0FreePtr o0 o1 + ⟨36⟩) ::
          ⟨1889567281⟩ :: amm4MintToken0Word σ I ::
          ⟨0⟩ :: amm4SwapToWord I :: q1 :: q0 :: ⟨349⟩ :: [sel])
        (amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2)
        (amm4SwapBalance0CalldataWords o0 o1)
        o2 (cA', σ') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g Apre I with accountMap := σ }
        (AccountAddress.ofUInt256 (amm4MintToken0Word σ I))
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ g Apre I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o2)
        false ∧ o2.size < UInt256.size ∧ o2.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd4361⟩ := hframe
  obtain ⟨cA', σ', z, o2, A_in, callGas, k', C', hΘpack,
    rd4362, hosz⟩ :=
    RD.solcStaticcall rd4361 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw := amm4SwapBalance0CallWords_same o0 o1
    hlo0 hbound0 hlo1 hbound1
  refine ⟨cA', σ', z, o2, A', k', C', ?_, ?_, hosz, ?_⟩
  · simpa [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      haw, amm4SwapBalance0PostCallMem] using rd4362
  · refine callCoincides (A_in := A_in) (g'' := g'')
      (callGas := callGas) (callPerm := false)
      (targetWord := amm4MintToken0Word σ I)
      (mem := amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
      (inOff := amm4SwapBalance0FreePtr o0 o1) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by
        rw [show I.depth = (1024 : Fin 1025) from h]
        decide))
      rfl (amm4SwapBalance0CalldataMem_encode I q0 q1
        hlo0 hbound0 hbound1) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((amm4SwapBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
          (amm4SwapBalance0FreePtr o0 o1).toNat 36).size = 36 := by
      rw [amm4SwapBalance0CalldataMem_read36 I q0 q1
        hlo0 hbound0 hbound1, ByteArray.size_append, toByteArray_size]
      decide
    have hinputBound :
        ((amm4SwapBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
          (amm4SwapBalance0FreePtr o0 o1).toNat 36).size ≤
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
      ((amm4SwapBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
        (amm4SwapBalance0FreePtr o0 o1).toNat 36)
      (I.depth + 1) I.header false
      (by simpa [initState] using hΘ) hinputBound

theorem amm4SwapX_balance0CallFailed {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨2919⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd4369 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨2933⟩, jumpiNT (by decide)]
  have rd4372 := evm_run rd4369 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd4373 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd4372 (by native_decide)
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
  have rd4375 := evm_run rd4373 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd4375 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem amm4SwapX_balance0CallSucceeded {cAstart gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 mem o2 : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2919⟩
      [⟨1⟩, amm4SwapBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken0Word σ I,
        ⟨0⟩, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw o2 acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2938⟩
      [⟨0⟩, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw o2 acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨2933⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

end Benchmarks.ActAmm4
