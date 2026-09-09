import Examples.NestedCaller.Blocks
import Examples.NestedCaller.Spec
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.EVMWord
import Reasoning.ExternalCall
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Stepping

namespace NestedCaller

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

abbrev runSelector : ByteArray := ⟨#[0x38, 0x1f, 0xd1, 0x90]⟩

theorem nestedCallerDispatch :
    SingleSelectorDispatch nestedCallerContract runTransition runSelector :=
  singleSelectorDispatch rfl rfl nestedCallerRunSelectorBytes rfl

theorem nestedCallerContains15 : (D_J nestedCallerBytecode 0).contains ⟨15⟩ = true := by
  jump_dest

theorem nestedCallerContains41 : (D_J nestedCallerBytecode 0).contains ⟨41⟩ = true := by
  jump_dest

theorem nestedCallerContains45 : (D_J nestedCallerBytecode 0).contains ⟨45⟩ = true := by
  jump_dest

theorem nestedCallerEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨941609360⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if (runSelector == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x38 0x1f 0xd1 0x90 ⟨941609360⟩ (by decide)

abbrev nestedCallerSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

abbrev nestedCallerFirstArmPc : UInt256 := ⟨30⟩

theorem nestedCallerArmWellFormed : armWellFormed nestedCallerBytecode nestedCallerFirstArmPc :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem nestedCallerArmSelNat :
    armSelNat nestedCallerBytecode nestedCallerFirstArmPc = ⟨941609360⟩ := by
  decide

theorem nestedCallerMatch_eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (armSelNat nestedCallerBytecode nestedCallerFirstArmPc) (nestedCallerSelWord I)
      = if (runSelector == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  rw [nestedCallerArmSelNat]
  exact nestedCallerEvmSelector hsz

theorem nestedCallerReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : (runSelector == I.calldata.extract 0 4) = true) :
    ∃ k C, RD nestedCallerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨45⟩
        [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := nestedCallerFirstArmPc) (bodyPC := ⟨45⟩) (i := 0)
    hcode hwv hsz hsize (by solc_dispatch_prefix) (by jump_dest)
    (fun j hj => by rw [Nat.le_zero.mp hj]; exact nestedCallerArmWellFormed)
    (fun j hj => absurd hj (by omega))
    (by
      show UInt256.eq (armSelNat nestedCallerBytecode nestedCallerFirstArmPc)
          (nestedCallerSelWord I) ≠ ⟨0⟩
      rw [nestedCallerMatch_eq I hsz, if_pos hmatch]
      decide)
    (by jump_dest) (by decide)

theorem nestedCallerX_callvalue_ne
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev nestedCallerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiNT (isZero_eq_zero_of_ne hwv),
      raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem nestedCallerX_cvz_prefix
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RD nestedCallerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
        [⟨41⟩, UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 14 53 := by
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiT (by rw [hwv]; decide) nestedCallerContains15,
      jumpdest, pop, push1 ⟨4⟩, calldatasize, lt, push2 ⟨41⟩ ]

theorem nestedCallerX_cvz_short
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev nestedCallerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (nestedCallerX_cvz_prefix hcode hwv) with [
    jumpiT (lt_four_ne_zero_of_lt hsz) nestedCallerContains41,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem nestedCallerX_cvz_noMatch
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : (runSelector == I.calldata.extract 0 4) = false) :
    RDrev nestedCallerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (nestedCallerX_cvz_prefix hcode hwv) with [
    jumpiNT (lt_four_eq_zero_of_ge hsz hsize),
    push0, calldataload, push1 ⟨224⟩, shr, dup1, push4 ⟨941609360⟩, eq, push2 ⟨45⟩,
    jumpiNT (by
      rw [show ((⟨0⟩ : UInt256).toNat) = 0 from by decide, nestedCallerEvmSelector hsz]
      simp [hmatch]),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem nestedCallerShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = nestedCallerBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor nestedCallerConfig nestedCallerContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (nestedCallerX_cvz_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch
    hcode (nestedCallerDispatch.none_short hsz)

theorem nestedCallerNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = nestedCallerBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hmatch : (runSelector == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor nestedCallerConfig nestedCallerContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (nestedCallerX_cvz_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hmatch)
      |>.reEquivNoDispatch hcode (nestedCallerDispatch.none_nomatch hmatch)
  · have hshort : I.calldata.size < 4 := by omega
    exact nestedCallerShortRevert hcode hsize hperm hwv hshort

theorem nestedCallerNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = nestedCallerBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor nestedCallerConfig nestedCallerContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (nestedCallerX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivNonPayable
    hcode rfl rfl
    fun _ca => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end NestedCaller
