import Benchmarks.ActAmm4.Decode
import Benchmarks.ActAmm4.Trusted

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

abbrev amm4SwapAmount0Word (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev amm4SwapAmount1Word (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev amm4SwapToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨64⟩ : UInt256).toNat 32)

abbrev amm4SwapStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "amount0Out"
    (.int (Int.ofNat (amm4SwapAmount0Word I).toNat))).insert "amount1Out"
    (.int (Int.ofNat (amm4SwapAmount1Word I).toNat))).insert "to"
    (.address (AccountAddress.ofNat (amm4SwapToWord I).toNat))

theorem amm4Decode_swap_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata =
        some (amm4SwapStore I) := by
  show decodeCalldata ["amount0Out", "amount1Out", "to"]
      [uint256, uint256, addr] I.calldata = _
  simpa [addr, uint256, abiUInt256, amm4SwapStore, amm4SwapAmount0Word,
    amm4SwapAmount1Word, amm4SwapToWord, calldataWord] using
    amm4DecodeCalldata_uint256_uint256_address_ok
      (cd := I.calldata) (x := "amount0Out") (y := "amount1Out") (z := "to")
      hsz100 hbig hcanon

theorem amm4Decode_swap_none_noncanon {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4SwapToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["amount0Out", "amount1Out", "to"]
      [uint256, uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256, amm4SwapToWord, calldataWord] using
    amm4DecodeCalldata_uint256_uint256_address_none_noncanon
      (cd := I.calldata) (x := "amount0Out") (y := "amount1Out") (z := "to")
      hsz100 hbig hnc

theorem amm4Decode_swap_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["amount0Out", "amount1Out", "to"]
      [uint256, uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    amm4DecodeCalldata_uint256_uint256_address_none_short
      (cd := I.calldata) (x := "amount0Out") (y := "amount1Out") (z := "to")
      hsz4 hshort

theorem amm4Decode_swap_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["amount0Out", "amount1Out", "to"]
      [uint256, uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    amm4DecodeCalldata_uint256_uint256_address_none_huge
      (cd := I.calldata) (x := "amount0Out") (y := "amount1Out") (z := "to") hbig

theorem amm4SwapSelector_size {I : ExecutionEnv}
    (hsel : amm4SelIs I ⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem amm4Dispatch_swap {cd : ByteArray}
    (hsel : ((⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some swapTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, mintTransition])
    (post := [totalSupplyTransition, transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, amm4SwapSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, amm4AllowanceSelectorBytes, hcd]
    | rw [selectorOf, amm4ApproveSelectorBytes, hcd]
    | rw [selectorOf, amm4BalanceOfSelectorBytes, hcd]
    | rw [selectorOf, amm4BurnSelectorBytes, hcd]
    | rw [selectorOf, amm4MintSelectorBytes, hcd]
  all_goals decide

end Benchmarks.ActAmm4
