import Benchmarks.ActAmm.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

/-- Trusted selector of approve, from the checked-in solc artifact. -/
axiom ammApproveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr approveTransition))).extract 0 4 =
      ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩

/-- Trusted selector of burn, from the checked-in solc artifact. -/
axiom ammBurnSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr burnTransition))).extract 0 4 =
      ⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩

/-- Trusted selector of totalSupply, from the checked-in solc artifact. -/
axiom ammTotalSupplySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr totalSupplyTransition))).extract 0 4 =
      ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩

/-- Trusted selector of transferFrom, from the checked-in solc artifact. -/
axiom ammTransferFromSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr transferFromTransition))).extract 0 4 =
      ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩

/-- Trusted selector of swap1, from the checked-in solc artifact. -/
axiom ammSwap1SelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr swap1Transition))).extract 0 4 =
      ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩

/-- Trusted selector of mint, from the checked-in solc artifact. -/
axiom ammMintSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr mintTransition))).extract 0 4 =
      ⟨#[0x6a, 0x62, 0x78, 0x42]⟩

/-- Trusted selector of balanceOf, from the checked-in solc artifact. -/
axiom ammBalanceOfSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr balanceOfTransition))).extract 0 4 =
      ⟨#[0x70, 0xa0, 0x82, 0x31]⟩

/-- Trusted selector of transfer, from the checked-in solc artifact. -/
axiom ammTransferSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr transferTransition))).extract 0 4 =
      ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩

/-- Trusted selector of allowance, from the checked-in solc artifact. -/
axiom ammAllowanceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr allowanceTransition))).extract 0 4 =
      ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩

/-- Trusted selector of swap0, from the checked-in solc artifact. -/
axiom ammSwap0SelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr swap0Transition))).extract 0 4 =
      ⟨#[0x13, 0xbd, 0x59, 0xeb]⟩


end Benchmarks.ActAmm
