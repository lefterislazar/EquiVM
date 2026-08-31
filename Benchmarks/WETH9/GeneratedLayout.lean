import Solm.MetaSolidityLayout
import Benchmarks.WETH9.Spec

/-!
# Generated-layout equivalence for WETH9

WETH9 keeps custom Solidity 0.5 string read/write hooks, but its raw storage locations follow the
ordinary Solidity allocation rules.  These pointwise checks cover every path recognized by the
benchmark's hand-written `storageLayoutRaw` oracle.
-/

namespace Benchmarks.WETH9
open Solm ABI

def generatedStorageLayout : StorageLayout :=
  solidityLayout! [([] : List StructDecl)] [storageDecls]

example (evm : EVM.State) :
    generatedStorageLayout.layout { base := "name", steps := [.length] } evm =
      storageLayoutRaw { base := "name", steps := [.length] } evm := by
  rfl

example (evm : EVM.State) :
    generatedStorageLayout.layout { base := "symbol", steps := [.length] } evm =
      storageLayoutRaw { base := "symbol", steps := [.length] } evm := by
  rfl

example (evm : EVM.State) :
    generatedStorageLayout.layout { base := "decimals" } evm =
      storageLayoutRaw { base := "decimals" } evm := by
  rfl

example (evm : EVM.State) (owner : KeyValue) :
    generatedStorageLayout.layout { base := "balanceOf", steps := [.mindex owner] } evm =
      storageLayoutRaw { base := "balanceOf", steps := [.mindex owner] } evm := by
  rfl

example (evm : EVM.State) (owner spender : KeyValue) :
    generatedStorageLayout.layout
        { base := "allowance", steps := [.mindex owner, .mindex spender] } evm =
      storageLayoutRaw
        { base := "allowance", steps := [.mindex owner, .mindex spender] } evm := by
  rfl

end Benchmarks.WETH9
