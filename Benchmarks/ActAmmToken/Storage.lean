import Benchmarks.ActAmmToken.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmmToken

theorem tokenStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem tokenStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc, uint256Int] using storageLocStore_uint256 evm slot val

theorem tokenUint256ReturnEncoding (v : UInt256) :
    encodeReturnValue? uint256 (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := uint256ReturnEncoding v

theorem tokenConfig_storage_totalSupply :
    config.storage.layout { base := "totalSupply", steps := [] } =
      fun _ => some (wordLoc ⟨0⟩) := rfl

theorem tokenConfig_storage_balanceOf (owner : KeyValue) :
    config.storage.layout { base := "balanceOf", steps := [.mindex owner] } =
      fun _ => some (wordLoc (balanceOfSlot owner)) := rfl

theorem tokenConfig_storage_allowance (owner spender : KeyValue) :
    config.storage.layout
      { base := "allowance", steps := [.mindex owner, .mindex spender] } =
      fun _ => some (wordLoc (allowanceSlot owner spender)) := rfl

end Benchmarks.ActAmmToken
