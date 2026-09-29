import Benchmarks.ActAmm4.Common
import Benchmarks.ActAmm4.Decode
import Benchmarks.ActAmm4.Trusted
import Benchmarks.ActAmm4.Routines
import Benchmarks.ActAmm4.MintSourceArithmetic
import Benchmarks.ActAmm4.Transfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev amm4BurnLiquidityWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev amm4BurnToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev amm4BurnStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "liquidity"
    (.int (Int.ofNat (amm4BurnLiquidityWord I).toNat))).insert "to"
    (.address (AccountAddress.ofNat (amm4BurnToWord I).toNat))

theorem amm4Decode_burn_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4BurnToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata =
        some (amm4BurnStore I) := by
  show decodeCalldata ["liquidity", "to"] [uint256, addr] I.calldata = _
  simpa [addr, uint256, abiUInt256, amm4BurnStore,
    amm4BurnLiquidityWord, amm4BurnToWord, calldataWord] using
    amm4DecodeCalldata_uint256_address_ok (cd := I.calldata)
      (x := "liquidity") (y := "to") hsz68 hbig hcanon

theorem amm4Decode_burn_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["liquidity", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    amm4DecodeCalldata_uint256_address_none_short
      (cd := I.calldata) (x := "liquidity") (y := "to") hsz4 hshort

theorem amm4Decode_burn_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["liquidity", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    amm4DecodeCalldata_uint256_address_none_huge
      (cd := I.calldata) (x := "liquidity") (y := "to") hbig

theorem amm4Decode_burn_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4BurnToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["liquidity", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, amm4BurnToWord] using
    amm4DecodeCalldata_uint256_address_none_noncanon
      (cd := I.calldata) (x := "liquidity") (y := "to") hsz68 hbig hnc

theorem amm4BurnSelector_size {I : ExecutionEnv}
    (hsel : amm4SelIs I ⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem amm4Dispatch_burn {cd : ByteArray}
    (hsel : ((⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some burnTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition])
    (post := [mintTransition, swapTransition,
      totalSupplyTransition, transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, amm4BurnSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, amm4AllowanceSelectorBytes, hcd]
    | rw [selectorOf, amm4ApproveSelectorBytes, hcd]
    | rw [selectorOf, amm4BalanceOfSelectorBytes, hcd]
  all_goals decide

end Benchmarks.ActAmm4
