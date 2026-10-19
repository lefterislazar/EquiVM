import Solm.SolidityStorage

/-!
# Storage algorithms of the Solidity semantics

The Solidity semantics reads and writes storage with the algorithms below, over a storage layout
(`Solm.StorageLayout`, a state-independent locator; `Solidity.storageLayout` derives solc's).  The
layout is the only parameter: the algorithms are solc's via-IR code generator (solc ≥ 0.8.34;
`copy_*_to_storage`, `clear_*`, `resize_array`, `byte_array_*` in the generated Yul).  They use
the encodings of `Solm.SolidityStorage`: packed primitives (`storageLocLoad`/`storageLocStore`),
and the short/long form of `bytes`/`string` (header decoding, whole-value reads and writes).

On storage that Solidity code writes, every solc 0.8 release, via-IR or legacy, behaves the same
way.  Storage can also hold bytes that no value covers (written by inline assembly, a delegatecall,
or another compiler); there the via-IR behaviour is the one modelled:

* `delete` of an aggregate (struct, array, the tail of a dynamic array) zeroes the whole slot of
  every primitive in it (`clear_struct_storage`, `clear_storage_range`).  A primitive deleted on
  its own, or popped from an array, is zeroed in place.
* An array of primitives is written whole slots at a time, so the bytes after its last element
  are zero (`copy_array_to_storage`).  Assigning a dynamic array first clears the elements past
  the new length (`resize_array`) and overwrites the others.
* `push`/`pop` on `bytes`/`string` change the header and the affected byte in place
  (`byte_array_increase_size`, `array_push_from_t_bytes1`, `byte_array_pop`): `push()` exposes
  whatever byte the storage holds at the new position.

Results: `.revert` is a corrupt `bytes`/`string` header (`Panic(0x22)`) or `pop` on an empty array
(`Panic(0x31)`); `.error` is an ill-formed program.  Behaviour across compiler versions and
pipelines: `scripts/solc_storage_audit/REPORT.md` on branch `solidity-storage-analysis`.
-/

namespace Solidity.Storage

open ABI Solm

/-- Value types: what a storage layout locates as a single leaf. -/
def isPrimitive : StorageType → Bool
  | .elem _ | .contract _ => true
  | _ => false

/-- Zero the whole slot that holds the primitive at `er` (`sstore(slot, 0)`). -/
def zeroLeafSlot (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) :
    EvalResult EVM.State := do
  let loc ← EvalResult.ofOption .storageError (solidityLeafLoc? layout er evm)
  pure (Solm.EVM.storageStore evm evm.executionEnv.codeOwner loc.slot ⟨0⟩)

/-- solc's `array_convert_length_to_size` for primitives packed `perSlot` to a slot: the number of
    slots `n` elements occupy, in the 256-bit arithmetic of the generated code (a corrupt length
    near `2^256` wraps). -/
def slotsFor (perSlot n : Nat) : Nat :=
  if perSlot ≤ 1 then n % 2 ^ 256 else (n + perSlot - 1) % 2 ^ 256 / perSlot

/-- Zero `count` consecutive slots from `start` (`clear_storage_range`). -/
def zeroSlots (evm : EVM.State) (start : EVM.Word) : Nat → EVM.State
  | 0 => evm
  | n + 1 =>
      zeroSlots (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (start + Ethereum.UInt256.ofNat n) ⟨0⟩)
        start n

/-- Clear the slots from the one after element `lo - 1` up to the last slot of element `hi - 1`, of
    an array of primitives at `er` (`clear_storage_array`, `cleanup_storage_array_end`); nothing
    when `hi ≤ lo`.  A slot shared with the elements kept is left: assignment rewrites it. -/
def clearPrimitiveRange (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) (lo hi : Nat) :
    EvalResult EVM.State :=
  if hi ≤ lo then .ok evm
  else do
    let first ← EvalResult.ofOption .storageError
      (solidityLeafLoc? layout { er with steps := er.steps ++ [.aindex (.int 0)] } evm)
    let perSlot := 32 / first.size.val
    let start := slotsFor perSlot lo
    let count := (slotsFor perSlot hi + 2 ^ 256 - start) % 2 ^ 256
    pure (zeroSlots evm (first.slot + Ethereum.UInt256.ofNat start) count)

/-! ## Reading -/

mutual

/-- Read a typed value, reconstructing aggregates. -/
def readAt (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType → EvalResult Value
  | .elem _ | .contract _ => do
      let loc ← EvalResult.ofOption .storageError (solidityLeafLoc? layout er evm)
      pure (storageLocLoad evm loc)
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let values ← readFields layout evm er fields
      pure (.struct name values)
  | .tuple types => do
      let values ← readTuple layout evm er 0 types
      pure (.tuple values)
  | .array elem count => do
      let values ← readArray layout evm er elem 0 count
      pure (.array values)
  | .dynamicArray elem => do
      let length ← solidityDynamicLength? layout evm er
      let values ← readArray layout evm er elem 0 length
      pure (.array values)
  | .bytes | .string => solidityValueResultToEval (solidityReadBytesValue? layout er evm)
  termination_by ty => (sizeOf ty, 0)

def readFields (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) → EvalResult (List (Ident × Value))
  | [] => .ok []
  | (name, ty) :: rest => do
      let value ← readAt layout evm { er with steps := er.steps ++ [.field name] } ty
      let values ← readFields layout evm er rest
      pure ((name, value) :: values)
  termination_by fields => (sizeOf fields, 0)

def readTuple (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) (index : Nat) :
    List StorageType → EvalResult (List Value)
  | [] => .ok []
  | ty :: rest => do
      let value ← readAt layout evm { er with steps := er.steps ++ [.tupleElem index] } ty
      let values ← readTuple layout evm er (index + 1) rest
      pure (value :: values)
  termination_by types => (sizeOf types, 0)

def readArray (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef)
    (elem : StorageType) (index : Nat) : Nat → EvalResult (List Value)
  | 0 => .ok []
  | count + 1 => do
      let value ← readAt layout evm { er with steps := er.steps ++ [.aindex (.int index)] } elem
      let values ← readArray layout evm er elem (index + 1) count
      pure (value :: values)
  termination_by count => (sizeOf elem, count)

end

/-! ## Clearing -/

mutual

/-- `delete`: clear all enumerable storage occupied by `ty` at `er`.  Mappings are skipped because
their keys cannot be enumerated. -/
def clearAt (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType → EvalResult EVM.State
  | .elem _ | .contract _ => do
      let loc ← EvalResult.ofOption .storageError (solidityLeafLoc? layout er evm)
      EvalResult.ofOption .storageError (storageLocStore evm loc (.int 0))
  | .mapping _ _ => .ok evm
  | .struct _ fields => clearFields layout evm er fields
  | .tuple types => clearTuple layout evm er 0 types
  | .array elem count =>
      if isPrimitive elem then clearPrimitiveRange layout evm er 0 count
      else clearArray layout evm er elem 0 count
  | .dynamicArray elem => do
      let length ← solidityDynamicLength? layout evm er
      let evm' ← if isPrimitive elem then clearPrimitiveRange layout evm er 0 length
        else clearArray layout evm er elem 0 length
      let lenLoc ← EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
      EvalResult.ofOption .storageError (storageLocStore evm' lenLoc (.int 0))
  | .bytes | .string => solidityStateResultToEval (solidityPrepareBytesWrite? layout er 0 evm)
  termination_by ty => (sizeOf ty, 0)

def clearFields (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) → EvalResult EVM.State
  | [] => .ok evm
  | (name, ty) :: rest => do
      let er' := { er with steps := er.steps ++ [.field name] }
      let evm' ← if isPrimitive ty then zeroLeafSlot layout evm er' else clearAt layout evm er' ty
      clearFields layout evm' er rest
  termination_by fields => (sizeOf fields, 0)

def clearTuple (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) (index : Nat) :
    List StorageType → EvalResult EVM.State
  | [] => .ok evm
  | ty :: rest => do
      let er' := { er with steps := er.steps ++ [.tupleElem index] }
      let evm' ← if isPrimitive ty then zeroLeafSlot layout evm er' else clearAt layout evm er' ty
      clearTuple layout evm' er (index + 1) rest
  termination_by types => (sizeOf types, 0)

/-- Clear the `count` elements from index `start` on. -/
def clearArray (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef)
    (elem : StorageType) (start : Nat) : Nat → EvalResult EVM.State
  | 0 => .ok evm
  | count + 1 => do
      let er' := { er with steps := er.steps ++ [.aindex (.int (start + count : Nat))] }
      let evm' ← if isPrimitive elem then zeroLeafSlot layout evm er' else clearAt layout evm er' elem
      clearArray layout evm' er elem start count
  termination_by count => (sizeOf elem, count)

end

/-! ## Writing -/

mutual

/-- Write a typed value, recursively for aggregates. -/
def writeAt (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType → Value → EvalResult EVM.State
  | .elem _, value
  | .contract _, value => do
      let loc ← EvalResult.ofOption .storageError (solidityLeafLoc? layout er evm)
      EvalResult.ofOption .storageError (storageLocStore evm loc value)
  | .struct expected fields, .struct actual values =>
      if expected = actual then writeFields layout evm er fields values
      else .error .typeError
  | .tuple types, .tuple values => writeTuple layout evm er 0 types values
  | .array elem count, .array values =>
      if values.length = count then do
        -- arrays of primitives are copied whole slots at a time
        let evm' ← if isPrimitive elem then clearPrimitiveRange layout evm er 0 count else pure evm
        writeArray layout evm' er elem 0 values
      else .error .typeError
  | .dynamicArray elem, .array values => do
      let oldLength ← solidityDynamicLength? layout evm er
      -- `resize_array`: shrinking clears the elements past the new length; arrays of primitives
      -- are then copied whole slots at a time
      let evm2 ← if isPrimitive elem then do
          let evm1 ← clearPrimitiveRange layout evm er values.length oldLength
          clearPrimitiveRange layout evm1 er 0 values.length
        else clearArray layout evm er elem values.length (oldLength - values.length)
      let evm3 ← writeArray layout evm2 er elem 0 values
      let lenLoc ← EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
      EvalResult.ofOption .storageError (storageLocStore evm3 lenLoc (.int values.length))
  | .bytes, .bytes bytes
  | .string, .bytes bytes => solidityStateResultToEval (solidityWriteBytesValue? layout er bytes evm)
  | _, _ => .error .typeError
  termination_by ty => (sizeOf ty, 0)

def writeFields (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) → List (Ident × Value) → EvalResult EVM.State
  | [], [] => .ok evm
  | (name, ty) :: typeRest, (actual, value) :: valueRest =>
      if name = actual then do
        let evm' ← writeAt layout evm { er with steps := er.steps ++ [.field name] } ty value
        writeFields layout evm' er typeRest valueRest
      else .error .typeError
  | _, _ => .error .typeError
  termination_by types => (sizeOf types, 0)

def writeTuple (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef) (index : Nat) :
    List StorageType → List Value → EvalResult EVM.State
  | [], [] => .ok evm
  | ty :: typeRest, value :: valueRest => do
      let evm' ← writeAt layout evm { er with steps := er.steps ++ [.tupleElem index] } ty value
      writeTuple layout evm' er (index + 1) typeRest valueRest
  | _, _ => .error .typeError
  termination_by types => (sizeOf types, 0)

def writeArray (layout : StorageLayout) (evm : EVM.State) (er : EvaledStorageRef)
    (elem : StorageType) (index : Nat) : List Value → EvalResult EVM.State
  | [] => .ok evm
  | value :: rest => do
      let evm' ← writeAt layout evm { er with steps := er.steps ++ [.aindex (.int index)] } elem value
      writeArray layout evm' er elem (index + 1) rest
  termination_by values => (sizeOf elem, sizeOf values)

end

/-! ## `bytes`/`string` push and pop -/

/-- solc's `mask_bytes_dynamic`: keep the first `n` bytes of a word and zero the rest. -/
def maskBytes (word : EVM.Word) (n : Nat) : EVM.Word :=
  let low := 2 ^ (8 * (32 - n))
  Ethereum.UInt256.ofNat (word.toNat / low * low)

/-- solc's `extract_used_part_and_set_length_of_short_byte_array`: the header of a short value of
    length `n` whose bytes are the first `n` of `word`. -/
def shortBytesHeader (word : EVM.Word) (n : Nat) : EVM.Word :=
  Ethereum.UInt256.lor (maskBytes word n) (Ethereum.UInt256.ofNat (n * 2))

/-- Store byte `b` at position `index` of the value whose header is at `base`, in the form the
    current header selects. -/
def storeByte (evm : EVM.State) (base : EVM.Word) (index b : Nat) : StorageReadResult EVM.State :=
  match solidityByteLoc? evm base index with
  | some loc =>
      match storageLocStore evm loc (.int b) with
      | some evm' => .ok evm'
      | none => .error
  | none => .error

/-- `push()` (`byte_array_increase_size`): only the length grows.  A short value moving to the
    long form takes its 31 bytes into the first data word without the length byte. -/
def bytesPushZero (layout : StorageLayout) (er : EvaledStorageRef) (evm : EVM.State) :
    StorageReadResult EVM.State :=
  match solidityBytesBaseSlotAndLength? layout er evm with
  | .ok (base, len) =>
      let owner := evm.executionEnv.codeOwner
      let header := Solm.EVM.storageLoad evm owner base
      if 32 ≤ len then
        .ok (Solm.EVM.storageStore evm owner base (solidityBytesHeaderWord (len + 1)))
      else if len = 31 then
        let evm' := Solm.EVM.storageStore evm owner (solidityBytesDataSlot base 0) (maskBytes header 31)
        .ok (Solm.EVM.storageStore evm' owner base (solidityBytesHeaderWord 32))
      else
        .ok (Solm.EVM.storageStore evm owner base (shortBytesHeader header (len + 1)))
  | .revert => .revert
  | .error => .error

/-- `push(b)` (`array_push_from_t_bytes1`): the length grows by one and byte `b` is stored at the
    old length; the bytes after it are left as they are. -/
def bytesPush (layout : StorageLayout) (er : EvaledStorageRef) (b : Nat) (evm : EVM.State) :
    StorageReadResult EVM.State :=
  match solidityBytesBaseSlotAndLength? layout er evm with
  | .ok (base, len) =>
      let owner := evm.executionEnv.codeOwner
      let header := Solm.EVM.storageLoad evm owner base
      if len = 31 then
        let evm' := Solm.EVM.storageStore evm owner (solidityBytesDataSlot base 0) (maskBytes header 31)
        storeByte (Solm.EVM.storageStore evm' owner base (solidityBytesHeaderWord 32)) base 31 b
      else
        storeByte (Solm.EVM.storageStore evm owner base (header + Ethereum.UInt256.ofNat 2)) base len b
  | .revert => .revert
  | .error => .error

/-- `pop()` (`byte_array_pop`): reverts on an empty value; otherwise the last byte is zeroed and
    the length shrinks, moving a 32-byte value back into the header. -/
def bytesPop (layout : StorageLayout) (er : EvaledStorageRef) (evm : EVM.State) :
    StorageReadResult EVM.State :=
  match solidityBytesBaseSlotAndLength? layout er evm with
  | .ok (base, len) =>
      let owner := evm.executionEnv.codeOwner
      let header := Solm.EVM.storageLoad evm owner base
      if len = 0 then .revert
      else if len = 32 then
        let data := Solm.EVM.storageLoad evm owner (solidityBytesDataSlot base 0)
        let evm' := Solm.EVM.storageStore evm owner base (shortBytesHeader data 31)
        .ok (Solm.EVM.storageStore evm' owner (solidityBytesDataSlot base 0) ⟨0⟩)
      else if len < 32 then
        .ok (Solm.EVM.storageStore evm owner base (shortBytesHeader header (len - 1)))
      else
        match storeByte evm base (len - 1) 0 with
        | .ok evm' => .ok (Solm.EVM.storageStore evm' owner base (header - Ethereum.UInt256.ofNat 2))
        | .revert => .revert
        | .error => .error
  | .revert => .revert
  | .error => .error

/-! ## Operations -/

/-- The value of type `ty` at `er`. -/
def read (layout : StorageLayout) (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) :
    EvalResult Value :=
  readAt layout evm er ty

/-- Store `value`, of type `ty`, at `er`. -/
def write (layout : StorageLayout) (er : EvaledStorageRef) (ty : StorageType) (value : Value)
    (evm : EVM.State) : EvalResult EVM.State :=
  writeAt layout evm er ty value

/-- `delete`. -/
def clear (layout : StorageLayout) (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) :
    EvalResult EVM.State :=
  clearAt layout evm er ty

/-- `.length` of a fixed or dynamic array, `bytesN`, `bytes` or `string`. -/
def length (layout : StorageLayout) (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) :
    EvalResult Nat :=
  match ty with
  | .array _ count => .ok count
  | .elem (.bytes width) => .ok (fixedBytesSize width)
  | .dynamicArray _ => solidityDynamicLength? layout evm er
  | .bytes | .string =>
      match solidityReadBytesLength? layout er evm with
      | some result => solidityNatResultToEval result
      | none => .error .storageError
  | _ => .error .typeError

/-- `push`, with or without a value. -/
def push (layout : StorageLayout) (er : EvaledStorageRef) (ty : StorageType) (value : Option Value)
    (evm : EVM.State) : EvalResult EVM.State :=
  match ty with
  | .dynamicArray elem => do
      let length ← solidityDynamicLength? layout evm er
      let lenLoc ← EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
      let evm' ← EvalResult.ofOption .storageError (storageLocStore evm lenLoc (.int (length + 1)))
      match value with
      | some element => writeAt layout evm' { er with steps := er.steps ++ [.aindex (.int length)] } elem element
      | none => .ok evm'
  | .bytes | .string =>
      match value with
      | none => solidityStateResultToEval (bytesPushZero layout er evm)
      | some (.fixedBytes width [b]) =>
          if width.val = 0 then solidityStateResultToEval (bytesPush layout er b.toNat evm)
          else .error .typeError
      | some _ => .error .typeError
  | _ => .error .storageError

/-- `pop`: reverts on an empty array; the removed element is cleared. -/
def pop (layout : StorageLayout) (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) :
    EvalResult EVM.State :=
  match ty with
  | .dynamicArray elem => do
      let length ← solidityDynamicLength? layout evm er
      if length = 0 then .revert
      else do
        let newLength := length - 1
        let evm' ← clearAt layout evm { er with steps := er.steps ++ [.aindex (.int newLength)] } elem
        let lenLoc ← EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
        EvalResult.ofOption .storageError (storageLocStore evm' lenLoc (.int newLength))
  | .bytes | .string => solidityStateResultToEval (bytesPop layout er evm)
  | _ => .error .storageError

/-! ## Primitives and `bytes`/`string`

A primitive is read, written and deleted at its location; a `bytes`/`string` value is read,
written, measured and deleted with the encodings of `Solm.SolidityStorage`.  These operations
coincide with `Solm.solidityStorageBackend`, whose lemmas (`Reasoning.Theory`) therefore apply. -/

section Facts

variable {layout : StorageLayout} {er : EvaledStorageRef} {evm : EVM.State}

theorem read_elem {loc : StorageLoc} (hloc : layout er = some (.leaf loc)) (e : ElemType) (evm : EVM.State) :
    read layout er (.elem e) evm = .ok (storageLocLoad evm loc) := by
  simp [read, readAt, solidityLeafLoc?_of_leaf hloc, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem write_elem {loc : StorageLoc} (hloc : layout er = some (.leaf loc)) (e : ElemType) {value : Value}
    {evm' : EVM.State} (hstore : storageLocStore evm loc value = some evm') :
    write layout er (.elem e) value evm = .ok evm' := by
  simp [write, writeAt, solidityLeafLoc?_of_leaf hloc, hstore, EvalResult.ofOption, EvalResult.bind, bind]

theorem clear_elem {loc : StorageLoc} (hloc : layout er = some (.leaf loc)) (e : ElemType)
    {evm' : EVM.State} (hstore : storageLocStore evm loc (.int 0) = some evm') :
    clear layout er (.elem e) evm = .ok evm' := by
  simp [clear, clearAt, solidityLeafLoc?_of_leaf hloc, hstore, EvalResult.ofOption, EvalResult.bind, bind]

theorem length_eq_solm (ty : StorageType) :
    length layout er ty evm = (solidityStorageBackend layout).length er ty evm := rfl

theorem read_string_eq_solm :
    read layout er .string evm = (solidityStorageBackend layout).read er .string evm := by
  simp [read, readAt, solidityStorageBackend, solidityReadStorage?]

theorem write_string_eq_solm (value : Value) :
    write layout er .string value evm = (solidityStorageBackend layout).write er .string value evm := by
  cases value <;> simp [write, writeAt, solidityStorageBackend, solidityWriteStorage?]

theorem clear_string_eq_solm :
    clear layout er .string evm = (solidityStorageBackend layout).clear er .string evm := by
  simp [clear, clearAt, solidityStorageBackend, solidityClearStorage?]

theorem push_dynArray_none_eq_solm (st : StorageType) :
    push layout er (.dynamicArray st) none evm = (solidityStorageBackend layout).push er (.dynamicArray st) none evm := by
  simp [push, solidityStorageBackend, solidityPushStorage?]

end Facts

end Solidity.Storage
