import Benchmarks.ActAmm.Common
import Benchmarks.ActAmm.Decode
import Benchmarks.ActAmm.Trusted
import Benchmarks.ActAmm.Routines
import Benchmarks.ActAmm.MintSourceArithmetic
import Benchmarks.ActAmm.Transfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev ammBurnLiquidityWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev ammBurnToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev ammBurnStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "liquidity"
    (.int (Int.ofNat (ammBurnLiquidityWord I).toNat))).insert "to"
    (.address (AccountAddress.ofNat (ammBurnToWord I).toNat))

theorem ammDecode_burn_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammBurnToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata =
        some (ammBurnStore I) := by
  show decodeCalldata ["liquidity", "to"] [uint256, addr] I.calldata = _
  simpa [addr, uint256, abiUInt256, ammBurnStore,
    ammBurnLiquidityWord, ammBurnToWord, calldataWord] using
    ammDecodeCalldata_uint256_address_ok (cd := I.calldata)
      (x := "liquidity") (y := "to") hsz68 hbig hcanon

theorem ammDecode_burn_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["liquidity", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    ammDecodeCalldata_uint256_address_none_short
      (cd := I.calldata) (x := "liquidity") (y := "to") hsz4 hshort

theorem ammDecode_burn_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["liquidity", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    ammDecodeCalldata_uint256_address_none_huge
      (cd := I.calldata) (x := "liquidity") (y := "to") hbig

theorem ammDecode_burn_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammBurnToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["liquidity", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, ammBurnToWord] using
    ammDecodeCalldata_uint256_address_none_noncanon
      (cd := I.calldata) (x := "liquidity") (y := "to") hsz68 hbig hnc

theorem ammBurnSelector_size {I : ExecutionEnv}
    (hsel : ammSelIs I ⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ammDispatch_burn {cd : ByteArray}
    (hsel : ((⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some burnTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition])
    (post := [mintTransition, swap0Transition, swap1Transition,
      totalSupplyTransition, transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, ammBurnSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, ammAllowanceSelectorBytes, hcd]
    | rw [selectorOf, ammApproveSelectorBytes, hcd]
    | rw [selectorOf, ammBalanceOfSelectorBytes, hcd]
  all_goals decide

end Benchmarks.ActAmm
