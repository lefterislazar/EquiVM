import Solm.Semantics.StorageOps

/-!
# Laws for operation-owned storage backends

The law bundle is deliberately separate from `Config`: execution only needs operations, while
generic metatheory can request the laws it uses. Collision assumptions are expressed over bounded
regions of final 256-bit slots rather than as a false global injectivity axiom for Keccak.
-/

namespace Solm
open ABI

private def validIntValue : IntType -> Int -> Bool
  | .uint bits, value => decide (0 ≤ value ∧ value < (EVM.twoPow bits.val : Nat))
  | .sint bits, value =>
      decide (-(EVM.twoPow (bits.val - 1) : Int) ≤ value ∧
        value < (EVM.twoPow (bits.val - 1) : Nat))

private def validElemValue : ElemType -> Value -> Bool
  | .bool, .bool _ => true
  | .address, .address _ => true
  | .int ty, .int value => validIntValue ty value
  | .bytes n, .fixedBytes m bytes => n = m && bytes.length = n.val + 1
  | .fixed _, _ | .function, _ => false
  | _, _ => false

mutual
/-- Decidable shape/range predicate used by the read-after-write law. Unsupported fixed-point and
    function values are rejected instead of reaching the partial `wordToElem` cases. -/
def validStorageValue : StorageType -> Value -> Bool
  | .elem ty, value => validElemValue ty value
  | .contract _, .address _ => true
  | .struct expected fields, .struct actual values =>
      expected = actual && validStorageFields fields values
  | .tuple types, .tuple values => validStorageValues types values
  | .array elem count, .array values =>
      values.length = count && values.all (validStorageValue elem)
  | .dynamicArray elem, .array values => values.all (validStorageValue elem)
  | .bytes, .bytes _ | .string, .bytes _ => true
  | _, _ => false

def validStorageFields : List (Ident × StorageType) -> List (Ident × Value) -> Bool
  | [], [] => true
  | (name, ty) :: types, (actual, value) :: values =>
      name = actual && validStorageValue ty value && validStorageFields types values
  | _, _ => false

def validStorageValues : List StorageType -> List Value -> Bool
  | [], [] => true
  | ty :: types, value :: values =>
      validStorageValue ty value && validStorageValues types values
  | _, _ => false
end

/-- Length observed after clearing a length-bearing value. -/
def clearedStorageLength? : StorageType -> Option Nat
  | .array _ n => some n
  | .elem (.bytes n) => some (fixedBytesSize n)
  | .dynamicArray _ | .bytes | .string => some 0
  | _ => none

/-- Algebraic contract of a storage backend. `separated` describes references whose occupied
    physical regions do not overlap in the supplied state. -/
structure StorageLaws (backend : StorageBackend) where
  /-- State invariant required by the backend (for the EVM adapter this includes presence of the
      contract account being updated). -/
  admissible : EVM.State -> Prop
  separated : EVM.State -> EvaledStorageRef -> StorageType ->
    EvaledStorageRef -> StorageType -> Prop
  read_after_write : ∀ {evm evm' er ty value},
    admissible evm ->
    validStorageValue ty value = true ->
    backend.write er ty value evm = .ok evm' ->
    backend.read er ty evm' = .ok value
  read_after_write_separated : ∀ {evm evm' writtenRef writtenTy value readRef readTy},
    admissible evm ->
    separated evm writtenRef writtenTy readRef readTy ->
    backend.write writtenRef writtenTy value evm = .ok evm' ->
    backend.read readRef readTy evm' = backend.read readRef readTy evm
  read_after_clear : ∀ {evm evm' er ty defaultValue},
    admissible evm ->
    defaultValue? ty = .ok defaultValue ->
    backend.clear er ty evm = .ok evm' ->
    backend.read er ty evm' = .ok defaultValue
  read_after_clear_separated : ∀ {evm evm' clearedRef clearedTy readRef readTy},
    admissible evm ->
    separated evm clearedRef clearedTy readRef readTy ->
    backend.clear clearedRef clearedTy evm = .ok evm' ->
    backend.read readRef readTy evm' = backend.read readRef readTy evm
  length_after_clear : ∀ {evm evm' er ty expected},
    admissible evm ->
    clearedStorageLength? ty = some expected ->
    backend.clear er ty evm = .ok evm' ->
    backend.length er ty evm' = .ok expected
  length_after_push : ∀ {evm evm' er ty value oldLength},
    admissible evm ->
    backend.length er ty evm = .ok oldLength ->
    backend.push er ty value evm = .ok evm' ->
    backend.length er ty evm' = .ok (oldLength + 1)
  pop_empty : ∀ {evm er ty},
    admissible evm ->
    backend.length er ty evm = .ok 0 -> backend.pop er ty evm = .revert
  length_after_pop : ∀ {evm evm' er ty oldLength},
    admissible evm ->
    backend.length er ty evm = .ok oldLength ->
    backend.pop er ty evm = .ok evm' ->
    backend.length er ty evm' = .ok (oldLength - 1)
  write_preserves_admissible : ∀ {evm evm' er ty value},
    admissible evm -> backend.write er ty value evm = .ok evm' -> admissible evm'
  clear_preserves_admissible : ∀ {evm evm' er ty},
    admissible evm -> backend.clear er ty evm = .ok evm' -> admissible evm'
  push_preserves_admissible : ∀ {evm evm' er ty value},
    admissible evm -> backend.push er ty value evm = .ok evm' -> admissible evm'
  pop_preserves_admissible : ∀ {evm evm' er ty},
    admissible evm -> backend.pop er ty evm = .ok evm' -> admissible evm'

/-- Two bounded word regions are disjoint, with addition interpreted exactly as EVM word
    addition. This includes wraparound rather than silently assuming it cannot happen. -/
def WordRegionsDisjoint (base₁ : EVM.Word) (span₁ : Nat)
    (base₂ : EVM.Word) (span₂ : Nat) : Prop :=
  ∀ i < span₁, ∀ j < span₂,
    base₁ + Ethereum.UInt256.ofNat i ≠ base₂ + Ethereum.UInt256.ofNat j

/-- The precise assumption needed to separate two Keccak-derived storage regions. -/
def KeccakRegionsDisjoint (seed₁ : ByteArray) (span₁ : Nat)
    (seed₂ : ByteArray) (span₂ : Nat) : Prop :=
  WordRegionsDisjoint
    (Ethereum.uInt256OfByteArray (ffi.KEC seed₁)) span₁
    (Ethereum.uInt256OfByteArray (ffi.KEC seed₂)) span₂

/-- The separate assumption needed when a hash-derived region may overlap ordinary static slots. -/
def KeccakRegionDisjointFromStatic (seed : ByteArray) (hashSpan : Nat)
    (staticBase : EVM.Word) (staticSpan : Nat) : Prop :=
  WordRegionsDisjoint (Ethereum.uInt256OfByteArray (ffi.KEC seed)) hashSpan
    staticBase staticSpan

end Solm
