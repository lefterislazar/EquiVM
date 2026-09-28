import Benchmarks.ActAmm.Swap1Balance0Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1X_balance0Staticcall
    {cAstart cA gh bl σstart σ σ₀ A Apre I}
    {g : Sat256} {sel : UInt256} {out : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hdepth : I.depth.val < 1024)
    (hframe : ∃ (gasWord : UInt256) (k C : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3190⟩
      [gasWord, ammMintToken0Word σ I,
        ammMintToken0FreePtr out, ⟨36⟩,
        ammMintToken0FreePtr out, ⟨32⟩,
        ammMintToken0FreePtr out + ⟨36⟩, ⟨1889567281⟩,
        ammMintToken0Word σ I, ⟨0⟩,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0CalldataMem I out)
      (ammSwap1Balance0CalldataWords out) out (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (ret : ByteArray) (A' : Substate) (k' C' : Nat),
      RD ammBytecode I g
        (initState cAstart gh bl σstart σ₀ g A I) ⟨3191⟩
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          (ammMintToken0FreePtr out + ⟨36⟩) ::
          ⟨1889567281⟩ :: ammMintToken0Word σ I ::
          ⟨0⟩ :: ammSwap1ToWord I ::
          ammSwap1AmountWord I :: ⟨340⟩ :: [sel])
        (ammSwap1Balance0PostCallMem I out ret)
        (ammSwap1Balance0CalldataWords out)
        ret (cA', σ') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g Apre I with accountMap := σ }
        (AccountAddress.ofUInt256 (ammMintToken0Word σ I))
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ g Apre I with
          accountMap := σ', substate := A', createdAccounts := cA' }, ret)
        false ∧ ret.size < UInt256.size ∧ ret.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd1377⟩ := hframe
  obtain ⟨cA', σ', z, ret, A_in, callGas, k', C', hΘpack,
    rd1378, hretsz⟩ :=
    RD.solcStaticcall rd1377 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw := ammSwap1Balance0CallWords_same out hlo hbound
  refine ⟨cA', σ', z, ret, A', k', C', ?_, ?_, hretsz, ?_⟩
  · simpa [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      haw, ammSwap1Balance0PostCallMem] using rd1378
  · refine callCoincides (A_in := A_in) (g'' := g'')
      (callGas := callGas) (callPerm := false)
      (targetWord := ammMintToken0Word σ I)
      (mem := ammSwap1Balance0CalldataMem I out)
      (inOff := ammMintToken0FreePtr out) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by
        rw [show I.depth = (1024 : Fin 1025) from h]
        decide))
      rfl (ammSwap1Balance0CalldataMem_encode I hlo hbound) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((ammSwap1Balance0CalldataMem I out).readWithPadding
          (ammMintToken0FreePtr out).toNat 36).size = 36 := by
      rw [ammSwap1Balance0CalldataMem_read36 I hlo hbound,
        ByteArray.size_append, toByteArray_size]
      decide
    have hinputBound :
        ((ammSwap1Balance0CalldataMem I out).readWithPadding
          (ammMintToken0FreePtr out).toNat 36).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA gh bl σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (ammMintToken0Word σ I))
      (toExecute σ (AccountAddress.ofUInt256 (ammMintToken0Word σ I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((ammSwap1Balance0CalldataMem I out).readWithPadding
        (ammMintToken0FreePtr out).toNat 36)
      (I.depth + 1) I.header false
      (by simpa [initState] using hΘ) hinputBound

theorem ammSwap1X_balance0CallFailed
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨3191⟩ (⟨0⟩ :: R) mem aw ret acc k C)
    (hretsz : ret.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1385 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3205⟩, jumpiNT (by decide)]
  have rd1388 := evm_run rd1385 with [returndatasize, push0, push0]
  let len := UInt256.ofNat ret.size
  let memout := ret.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd1389 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd1388 (by native_decide)
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
  have rd1391 := evm_run rd1389 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd1391 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem ammSwap1X_balance0CallSucceeded
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {token0 : UInt256}
    {recipient amount fp : UInt256} {mem o : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3191⟩
      [⟨1⟩, fp + ⟨36⟩, ⟨1889567281⟩, token0,
        ⟨0⟩, recipient, amount, ⟨340⟩, sel]
      mem aw o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3210⟩
      [⟨0⟩, recipient, amount, ⟨340⟩, sel]
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3205⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

end Benchmarks.ActAmm
