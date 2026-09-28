import Benchmarks.ActAmm.BurnBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev ammSwap0AmountWord (I : ExecutionEnv) : UInt256 :=
  ammBurnLiquidityWord I

abbrev ammSwap0ToWord (I : ExecutionEnv) : UInt256 :=
  ammBurnToWord I

abbrev ammSwap0Store (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "amount1Out"
    (.int (Int.ofNat (ammSwap0AmountWord I).toNat))).insert "to"
    (.address (AccountAddress.ofNat (ammSwap0ToWord I).toNat))

theorem ammDecode_swap0_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (swap0Transition.params.map Param.name)
      (transitionSignature swap0Transition).paramTypes I.calldata =
      some (ammSwap0Store I) := by
  show decodeCalldata ["amount1Out", "to"] [uint256, addr]
    I.calldata = _
  simpa [addr, uint256, abiUInt256, ammSwap0Store,
    ammSwap0AmountWord, ammSwap0ToWord,
    ammBurnLiquidityWord, ammBurnToWord, calldataWord] using
    ammDecodeCalldata_uint256_address_ok (cd := I.calldata)
      (x := "amount1Out") (y := "to") hsz68 hbig hcanon

theorem ammDecode_swap0_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (swap0Transition.params.map Param.name)
      (transitionSignature swap0Transition).paramTypes I.calldata = none := by
  show decodeCalldata ["amount1Out", "to"] [uint256, addr]
    I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    ammDecodeCalldata_uint256_address_none_short
      (cd := I.calldata) (x := "amount1Out") (y := "to")
      hsz4 hshort

theorem ammDecode_swap0_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (swap0Transition.params.map Param.name)
      (transitionSignature swap0Transition).paramTypes I.calldata = none := by
  show decodeCalldata ["amount1Out", "to"] [uint256, addr]
    I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    ammDecodeCalldata_uint256_address_none_huge
      (cd := I.calldata) (x := "amount1Out") (y := "to") hbig

theorem ammDecode_swap0_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammSwap0ToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (swap0Transition.params.map Param.name)
      (transitionSignature swap0Transition).paramTypes I.calldata = none := by
  show decodeCalldata ["amount1Out", "to"] [uint256, addr]
    I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord,
    ammSwap0ToWord, ammBurnToWord] using
    ammDecodeCalldata_uint256_address_none_noncanon
      (cd := I.calldata) (x := "amount1Out") (y := "to")
      hsz68 hbig hnc

theorem ammSwap0Selector_size {I : ExecutionEnv}
    (hsel : ammSelIs I ⟨#[0x13, 0xbd, 0x59, 0xeb]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x13, 0xbd, 0x59, 0xeb]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ammDispatch_swap0 {cd : ByteArray}
    (hsel : ((⟨#[0x13, 0xbd, 0x59, 0xeb]⟩ : ByteArray) ==
      cd.extract 0 4) = true) :
    dispatchMsg contract cd = some swap0Transition := by
  have hcd : cd.extract 0 4 =
      (⟨#[0x13, 0xbd, 0x59, 0xeb]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition,
      balanceOfTransition, burnTransition, mintTransition])
    (post := [swap1Transition, totalSupplyTransition,
      transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, ammSwap0SelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, ammAllowanceSelectorBytes, hcd]
    | rw [selectorOf, ammApproveSelectorBytes, hcd]
    | rw [selectorOf, ammBalanceOfSelectorBytes, hcd]
    | rw [selectorOf, ammBurnSelectorBytes, hcd]
    | rw [selectorOf, ammMintSelectorBytes, hcd]
  all_goals decide

end Benchmarks.ActAmm
