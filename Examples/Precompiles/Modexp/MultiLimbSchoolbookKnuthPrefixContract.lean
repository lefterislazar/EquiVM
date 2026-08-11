import Examples.Precompiles.Modexp.MultiLimbClzCaller
import Examples.Precompiles.Modexp.MultiLimbSchoolbookKnuthSetupContract

/-!
# Composed Knuth setup through `_clz`

The local schoolbook contracts already proved each allocation and checked-address helper, but the
multi-limb branch still had no executable composition across them.  This module carries PC 5287
through quotient allocation, normalized-dividend allocation, the real `MCOPY`, and the deployed
`_clz` helper.  It keeps each free-pointer/layout obligation explicit and computes the shift from
the top divisor word loaded from EVM memory.  The dividend bound includes all 32 input limbs; this
requires the allocator contract to cover Solidity's 33-word `u` temporary rather than excluding
the maximum-size input for a proof-only bound.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookKnuthPrefix

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numQ (m kEff : Nat) : Nat := m - kEff + 1

def quotientMemory (mem : ByteArray) (fp m kEff : Nat) : ByteArray :=
  MultiLimbSchoolbookKnuthSetup.quotientMemory mem fp (numQ m kEff)

def quotientWords (aw : UInt256) (fp m kEff : Nat) : UInt256 :=
  MultiLimbSchoolbookKnuthSetup.quotientWords aw fp (numQ m kEff)

def uMemory (mem : ByteArray) (quotientFp uFp m kEff : Nat) : ByteArray :=
  MultiLimbSchoolbookKnuthSetup.uMemory
    (quotientMemory mem quotientFp m kEff) uFp m

def uWords (aw : UInt256) (quotientFp uFp m kEff : Nat) : UInt256 :=
  MultiLimbSchoolbookKnuthSetup.uWords
    (quotientWords aw quotientFp m kEff) uFp m

def copiedMemory (mem : ByteArray)
    (quotientFp uFp dividendPtr m kEff : Nat) : ByteArray :=
  MultiLimbSchoolbookKnuthSetup.copiedUMemory
    (uMemory mem quotientFp uFp m kEff) uFp dividendPtr m

def copiedWords (aw : UInt256)
    (quotientFp uFp dividendPtr m kEff : Nat) : UInt256 :=
  MultiLimbSchoolbookKnuthSetup.copiedUWords
    (uWords aw quotientFp uFp m kEff) uFp dividendPtr m

def topAddress (divisor : UInt256) (kEff : Nat) : UInt256 :=
  MultiLimbOddCompare.elementPtr divisor (UInt256.ofNat (kEff - 1))

def divisorHeaderWords (aw : UInt256)
    (quotientFp uFp dividendPtr m kEff : Nat) (divisor : UInt256) : UInt256 :=
  MultiLimbOddCompare.afterHeader
    (copiedWords aw quotientFp uFp dividendPtr m kEff) divisor

def finalWords (aw : UInt256)
    (quotientFp uFp dividendPtr m kEff : Nat) (divisor : UInt256) : UInt256 :=
  MultiLimbClz.afterTopLoad
    (divisorHeaderWords aw quotientFp uFp dividendPtr m kEff divisor)
    (topAddress divisor kEff)

def clzResultOf (mem : ByteArray) (aw : UInt256)
    (quotientFp uFp dividendPtr m kEff : Nat) (divisor : UInt256) :
    MultiLimbClz.StageResult :=
  MultiLimbClz.clzResult
    (MultiLimbClz.loadedTopWord
      (copiedMemory mem quotientFp uFp dividendPtr m kEff)
      (divisorHeaderWords aw quotientFp uFp dividendPtr m kEff divisor)
      (topAddress divisor kEff))

def totalSteps (mem : ByteArray) (aw : UInt256)
    (quotientFp uFp dividendPtr m kEff : Nat) (divisor : UInt256) : Nat :=
  268 + (clzResultOf mem aw quotientFp uFp dividendPtr m kEff divisor).steps

def totalGas (mem : ByteArray) (aw : UInt256)
    (quotientFp uFp dividendPtr m kEff : Nat) (divisor : UInt256) : Nat :=
  let qAw := quotientWords aw quotientFp m kEff
  let uAw' := uWords aw quotientFp uFp m kEff
  let copiedAw := copiedWords aw quotientFp uFp dividendPtr m kEff
  let headerAw := divisorHeaderWords aw quotientFp uFp dividendPtr m kEff divisor
  let result := clzResultOf mem aw quotientFp uFp dividendPtr m kEff divisor
  308 + MultiLimbSchoolbookKnuthSetup.quotientAllocationGas aw quotientFp (numQ m kEff) +
    MultiLimbSchoolbookKnuthSetup.uAllocationGas qAw uFp m +
    MultiLimbSchoolbookKnuthSetup.copyUGas uAw' uFp dividendPtr m +
    (Cₘ headerAw - Cₘ copiedAw) +
    (Cₘ (MultiLimbClz.afterTopLoad headerAw (topAddress divisor kEff)) - Cₘ headerAw) +
    result.gas

/-- Complete the multi-limb setup from the size-check successor through `_clz`. -/
theorem exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed quotientFp uFp dividendPtr ret m kEff : Nat}
    {tail : List UInt256} {rem divisor : UInt256}
    (hkEffPos : 0 < kEff) (hkEffLe : kEff ≤ m) (hmBound : m ≤ 65)
    (hquotientFp : 96 ≤ quotientFp)
    (hquotientBound : quotientFp + wordArrayAllocationSize (numQ m kEff) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ quotientFp)
    (hquotientGap : quotientFp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hquotientFree : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat quotientFp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (huFp : 96 ≤ uFp)
    (huBound : uFp + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hqMemSize : 96 ≤ (quotientMemory mem quotientFp m kEff).size)
    (hqMemLe : (quotientMemory mem quotientFp m kEff).size ≤ uFp)
    (huGap : uFp - (quotientMemory mem quotientFp m kEff).size < USize.size)
    (hqAw3 : 3 ≤ (quotientWords aw quotientFp m kEff).toNat)
    (hqAw64 : ¬ (⟨64⟩ : UInt256) ≥ quotientWords aw quotientFp m kEff * ⟨32⟩)
    (huFree : (quotientMemory mem quotientFp m kEff).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat uFp))
    (hdividendPtr32 : dividendPtr + 32 < UInt256.size)
    (huFp32 : uFp + 32 < UInt256.size)
    (hdivisorHeader : MultiLimbOddCompare.headerWord
      (copiedMemory mem quotientFp uFp dividendPtr m kEff)
      (copiedWords aw quotientFp uFp dividendPtr m kEff) divisor =
        UInt256.ofNat kEff)
    (htail : tail.length ≤ 997)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5287⟩
      (UInt256.ofNat kEff :: UInt256.ofNat m :: rem :: UInt256.ofNat dividendPtr ::
        UInt256.ofNat ret :: divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    let result := clzResultOf mem aw quotientFp uFp dividendPtr m kEff divisor
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat result.n :: rem :: UInt256.ofNat ret :: UInt256.ofNat kEff ::
        UInt256.ofNat m :: UInt256.ofNat quotientFp :: UInt256.ofNat uFp ::
        UInt256.ofNat (numQ m kEff) :: divisor :: tail)
      (copiedMemory mem quotientFp uFp dividendPtr m kEff)
      (finalWords aw quotientFp uFp dividendPtr m kEff divisor)
      rdata acc (steps + totalSteps mem aw quotientFp uFp dividendPtr m kEff divisor)
      (gasUsed + totalGas mem aw quotientFp uFp dividendPtr m kEff divisor) := by
  have hmWord : m < UInt256.size := by
    have : 65 < UInt256.size := by decide
    omega
  have hmSuccWord : m + 1 < UInt256.size := by
    have : 33 < UInt256.size := by decide
    omega
  have hkEffWord : kEff < UInt256.size := lt_of_le_of_lt hkEffLe hmWord
  have hnumQLe : numQ m kEff ≤ 65 := by
    unfold numQ
    omega
  have hnumQWord : numQ m kEff < UInt256.size := by
    have : 65 < UInt256.size := by decide
    omega
  have rd5314 := MultiLimbSchoolbookKnuthSetup.throughQuotientAllocationExact
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := mem) (aw := aw) (rdata := rdata) (acc := acc)
    (k := steps) (C := gasUsed) (fp := quotientFp) (m := m) (kEff := kEff)
    (tail := tail) (rem := rem) (dividend := UInt256.ofNat dividendPtr)
    (ret := UInt256.ofNat ret) (divisor := divisor)
    hkEffLe hmWord hnumQWord hnumQLe hquotientFp hquotientBound
    hmemSize hmemLe hquotientGap haw3 haw64 hquotientFree hcalldata
    (by omega) h
  have rd5327 := MultiLimbSchoolbookKnuthSetup.uAllocationExact
    (fp := uFp) (m := m) (kEff := kEff) (numQ := numQ m kEff)
    (tail := tail) hmSuccWord (by omega) huFp huBound hqMemSize hqMemLe
    huGap hqAw3 hqAw64 huFree hcalldata (by omega) (by
      simpa [quotientMemory, quotientWords, numQ] using rd5314)
  have hmBytes : 32 * m < UInt256.size := by
    have : 32 * 65 < UInt256.size := by decide
    omega
  have rd5356 := MultiLimbSchoolbookKnuthSetup.copyUAndTopIndexExact
    (fp := uFp) (dividend := dividendPtr) (m := m) (kEff := kEff)
    (numQ := numQ m kEff) (ret := ret) (tail := tail)
    hkEffPos hkEffWord hmBytes huFp32 hdividendPtr32 (by omega) (by
      simpa [uMemory, uWords, quotientMemory, quotientWords, numQ] using rd5327)
  have rd5362 := MultiLimbSchoolbookKnuthSetup.topDivisorAddressExact
    (fp := uFp) (m := m) (kEff := kEff) (numQ := numQ m kEff)
    (ret := ret) (tail := tail) hkEffPos hkEffWord hdivisorHeader
    (by omega) (by
      simpa [copiedMemory, copiedWords, uMemory, uWords, quotientMemory,
        quotientWords, numQ] using rd5356)
  have rd5368 := MultiLimbClz.loadTopAndClzExact
    (tail := rem :: UInt256.ofNat ret :: UInt256.ofNat kEff :: UInt256.ofNat m ::
      UInt256.ofNat quotientFp :: UInt256.ofNat uFp ::
      UInt256.ofNat (numQ m kEff) :: divisor :: tail)
    (by simp only [List.length_cons]; omega) (by
      simpa [topAddress] using rd5362)
  have normalized := rd5368.withIndices
    (k' := steps + totalSteps mem aw quotientFp uFp dividendPtr m kEff divisor)
    (C' := gasUsed + totalGas mem aw quotientFp uFp dividendPtr m kEff divisor)
    (by
      simp only [totalSteps, clzResultOf, divisorHeaderWords, topAddress]
      omega)
    (by
      simp only [totalGas, clzResultOf, divisorHeaderWords, copiedWords, uWords,
        quotientWords, topAddress, numQ]
      omega)
  simpa only [clzResultOf, finalWords, divisorHeaderWords, topAddress] using normalized

end Modexp.MultiLimbSchoolbookKnuthPrefix
