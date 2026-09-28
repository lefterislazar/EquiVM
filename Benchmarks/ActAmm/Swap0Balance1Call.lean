import Benchmarks.ActAmm.Swap0Balance1Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0X_balance1Staticcall
    {cAstart cA gh bl σstart σ σ₀ A Apre I}
    {g : Sat256} {sel : UInt256} {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138)
    (hdepth : I.depth.val < 1024)
    (hframe : ∃ (gasWord : UInt256) (k C : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨1533⟩
      [gasWord, ammMintToken1Word σ I,
        ammSwap0Balance1FreePtr out ret, ⟨36⟩,
        ammSwap0Balance1FreePtr out ret, ⟨32⟩,
        ammSwap0Balance1FreePtr out ret + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken1Word σ I,
        ⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0Balance1CalldataMem I out ret)
      (ammSwap0Balance1CalldataWords out ret) ret (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (ret1 : ByteArray) (A' : Substate) (k' C' : Nat),
      RD ammBytecode I g
        (initState cAstart gh bl σstart σ₀ g A I) ⟨1534⟩
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          (ammSwap0Balance1FreePtr out ret + ⟨36⟩) ::
          ⟨1889567281⟩ :: ammMintToken1Word σ I ::
          ⟨0⟩ :: UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)) ::
          ammSwap0ToWord I :: ammSwap0AmountWord I :: ⟨234⟩ :: [sel])
        (ammSwap0Balance1PostCallMem I out ret ret1)
        (ammSwap0Balance1CalldataWords out ret)
        ret1 (cA', σ') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g Apre I with accountMap := σ }
        (AccountAddress.ofUInt256 (ammMintToken1Word σ I))
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ g Apre I with
          accountMap := σ', substate := A', createdAccounts := cA' }, ret1)
        false ∧ ret1.size < UInt256.size ∧ ret1.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd1533⟩ := hframe
  obtain ⟨cA', σ', z, ret1, A_in, callGas, k', C', hΘpack,
    rd1534, hretsz⟩ :=
    RD.solcStaticcall rd1533 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw := ammSwap0Balance1CallWords_same out ret
    hlo hbound hretLo hretBound
  refine ⟨cA', σ', z, ret1, A', k', C', ?_, ?_, hretsz, ?_⟩
  · simpa [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      haw, ammSwap0Balance1PostCallMem] using rd1534
  · refine callCoincides (A_in := A_in) (g'' := g'')
      (callGas := callGas) (callPerm := false)
      (targetWord := ammMintToken1Word σ I)
      (mem := ammSwap0Balance1CalldataMem I out ret)
      (inOff := ammSwap0Balance1FreePtr out ret) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by
        rw [show I.depth = (1024 : Fin 1025) from h]
        decide))
      rfl (ammSwap0Balance1CalldataMem_encode I hlo hbound hretBound) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((ammSwap0Balance1CalldataMem I out ret).readWithPadding
          (ammSwap0Balance1FreePtr out ret).toNat 36).size = 36 := by
      rw [ammSwap0Balance1CalldataMem_read36 I hlo hbound hretBound,
        ByteArray.size_append, toByteArray_size]
      decide
    have hinputBound :
        ((ammSwap0Balance1CalldataMem I out ret).readWithPadding
          (ammSwap0Balance1FreePtr out ret).toNat 36).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA gh bl σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (ammMintToken1Word σ I))
      (toExecute σ (AccountAddress.ofUInt256 (ammMintToken1Word σ I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((ammSwap0Balance1CalldataMem I out ret).readWithPadding
        (ammSwap0Balance1FreePtr out ret).toNat 36)
      (I.depth + 1) I.header false
      (by simpa [initState] using hΘ) hinputBound

theorem ammSwap0X_balance1CallFailed
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1534⟩ (⟨0⟩ :: R) mem aw ret acc k C)
    (hretsz : ret.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1541 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨1548⟩, jumpiNT (by decide)]
  have rd1544 := evm_run rd1541 with [returndatasize, push0, push0]
  let len := UInt256.ofNat ret.size
  let memout := ret.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd1545 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd1544 (by native_decide)
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
  have rd1547 := evm_run rd1545 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd1547 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem ammSwap0X_balance1CallSucceeded
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {token1 : UInt256}
    {q0 recipient amount fp : UInt256} {mem o : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨1534⟩
      [⟨1⟩, fp + ⟨36⟩, ⟨1889567281⟩, token1,
        ⟨0⟩, q0, recipient, amount, ⟨234⟩, sel]
      mem aw o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨1553⟩
      [⟨0⟩, q0, recipient, amount, ⟨234⟩, sel]
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨1548⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

end Benchmarks.ActAmm
