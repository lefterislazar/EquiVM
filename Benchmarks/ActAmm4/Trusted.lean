import Benchmarks.ActAmm4.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

/-- Trusted allowance selector from the checked-in solc runtime dispatcher. -/
axiom amm4AllowanceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr allowanceTransition))).extract 0 4 =
      ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩

/-- Trusted approve selector from the checked-in solc runtime dispatcher. -/
axiom amm4ApproveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr approveTransition))).extract 0 4 =
      ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩

/-- Trusted balanceOf selector from the checked-in solc runtime dispatcher. -/
axiom amm4BalanceOfSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr balanceOfTransition))).extract 0 4 =
      ⟨#[0x70, 0xa0, 0x82, 0x31]⟩

/-- Trusted burn selector from the checked-in solc runtime dispatcher. -/
axiom amm4BurnSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr burnTransition))).extract 0 4 =
      ⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩

/-- Trusted mint selector from the checked-in solc runtime dispatcher. -/
axiom amm4MintSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr mintTransition))).extract 0 4 =
      ⟨#[0x6a, 0x62, 0x78, 0x42]⟩

/-- Trusted swap selector from the checked-in solc runtime dispatcher. -/
axiom amm4SwapSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr swapTransition))).extract 0 4 =
      ⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩

/-- Trusted totalSupply selector from the checked-in solc runtime dispatcher. -/
axiom amm4TotalSupplySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr totalSupplyTransition))).extract 0 4 =
      ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩

/-- Trusted transfer selector from the checked-in solc runtime dispatcher. -/
axiom amm4TransferSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr transferTransition))).extract 0 4 =
      ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩

/-- Trusted transferFrom selector from the checked-in solc runtime dispatcher. -/
axiom amm4TransferFromSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr transferFromTransition))).extract 0 4 =
      ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩

end Benchmarks.ActAmm4
