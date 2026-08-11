import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSCompareCoverage

/-! # Shared geometry for CIOS finalization -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbMontgomeryFinalize

structure CIOSFinalizeGeometry
    (columns : Nat) (mem : ByteArray)
    (aw nBefore tP bytes tEnd nP resultPtr resultBase : UInt256) : Prop where
  hColumnsPos : 0 < columns
  hBytes : bytes.toNat = 32 * columns
  hTEnd : tEnd.toNat = tP.toNat + 32 * columns
  hNOff : (⟨32⟩ + (bytes + nBefore)).toNat = nP.toNat + 32 * columns
  hSource : tP.toNat + 32 * columns ≤ mem.size
  hTopMem : tEnd.toNat + 32 ≤ mem.size
  hResult : resultPtr.toNat + 32 * columns ≤ mem.size
  hModulus : nP.toNat + 32 * columns ≤ mem.size
  hDisjoint : nP.toNat + 32 * columns ≤ resultPtr.toNat
  hTFit : tP.toNat + 32 * columns + 31 < UInt256.size
  hTopFit : tEnd.toNat + 32 + 31 < UInt256.size
  hNFit : nP.toNat + 32 * columns + 31 < UInt256.size
  hResultFit : resultPtr.toNat + 32 * columns + 31 < UInt256.size
  hCopyAccessFit : max resultPtr.toNat tP.toNat + bytes.toNat + 31 < UInt256.size
  hCopyStop : (⟨32⟩ + (bytes + resultBase)).toNat =
    resultPtr.toNat + 32 * columns
  hCovered : MemoryCovered mem aw
  hAwFit : aw.toNat * 32 < UInt256.size
  hReduced : limbsWithTop (memoryWordsFrom mem tP.toNat columns)
      (finalTopWord mem aw tEnd) <
    2 * Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)

end Modexp.MultiLimbMontgomeryCIOSSemantic
