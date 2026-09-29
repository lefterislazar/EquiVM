import Benchmarks.ActAmm4.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

/-- Loading a full-slot uint256 location agrees with the EVM storage word. -/
theorem amm4StorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc, uint256Int] using storageLocLoad_uint256 evm slot

/-- Writing a full-slot uint256 location agrees with the EVM storage update. -/
theorem amm4StorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc, uint256Int] using storageLocStore_uint256 evm slot val

end Benchmarks.ActAmm4
