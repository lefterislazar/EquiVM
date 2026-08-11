import Examples.Precompiles.Modexp.MultiLimbClzLoad

/-! # Exact caller wrapper for the deployed leading-zero helper -/
open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Load the selected top divisor limb, execute `_clz`, and return to the division setup. -/
theorem loadTopAndClzExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {address : UInt256}
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨5362⟩
      (address :: ⟨5368⟩ :: tail) mem aw rdata acc k C) :
    let result := clzResult (loadedTopWord mem aw address)
    RDx runtimeBytecode ee g s0 ⟨5368⟩ (UInt256.ofNat result.n :: tail)
      mem (afterTopLoad aw address) rdata acc
      (k + 4 + result.steps)
      (C + 15 + (Cₘ (afterTopLoad aw address) - Cₘ aw) + result.gas) := by
  have rd8042 := loadTopExact hdepth h
  have rd5368 := clzExact (by native_decide) (by omega) rd8042
  simpa only [Nat.add_assoc] using rd5368

end Modexp.MultiLimbClz
