import Examples.Precompiles.Modexp.MultiLimbClzExecutable

/-! # Exact load-and-call prefix for the deployed leading-zero helper -/
open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def loadedTopWord (mem : ByteArray) (aw address : UInt256) : UInt256 :=
  MultiLimbOddCompare.headerWord mem aw address

def afterTopLoad (aw address : UInt256) : UInt256 :=
  MultiLimbOddCompare.afterHeader aw address

theorem loadTopExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {address : UInt256}
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨5362⟩
      (address :: ⟨5368⟩ :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8042⟩
      (loadedTopWord mem aw address :: ⟨5368⟩ :: tail)
      mem (afterTopLoad aw address) rdata acc (k + 4)
      (C + 15 + (Cₘ (afterTopLoad aw address) - Cₘ aw)) := by
  have rd8042 := evm_run h with [
    jumpdest,
    mloadCanonical,
    pushCanonical 2 .PUSH2 ⟨8042⟩ (by decide),
    jump (by native_decide)
  ]
  rw [← MultiLimbOddCompare.headerWord_generated,
    ← MultiLimbOddCompare.afterHeader_generated] at rd8042
  have normalized := rd8042.withIndices
    (k' := k + 4)
    (C' := C + 15 + (Cₘ (MultiLimbOddCompare.afterHeader aw address) - Cₘ aw))
    (by omega) (by omega)
  simpa only [loadedTopWord, afterTopLoad] using normalized

end Modexp.MultiLimbClz
