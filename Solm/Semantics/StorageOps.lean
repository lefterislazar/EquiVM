import Solm.Semantics.Types
import Solm.Semantics.ValueOps

/-! Structured storage operations: typed read/write/clear/default over the opaque layout. -/

namespace Solm

open ABI

/-- The declared `StorageType` reached by following one evaled step from a value of type `t`. -/
def storageTypeStep? : StorageType -> EvaledStorageRefStep -> Option StorageType
  | .struct _ fields, .field name => (fields.find? (fun f => f.1 == name)).map (·.2)
  | .tuple ts, .tupleElem k => ts[k]?
  | .mapping _ v, .mindex _ => some v
  | .array t' _, .aindex _ => some t'
  | .dynamicArray t', .aindex _ => some t'
  | .bytes, .aindex _ => some (.elem (.int (.uint ⟨8, by decide⟩)))
  | .string, .aindex _ => some (.elem (.int (.uint ⟨8, by decide⟩)))
  | _, _ => none

/-- The declared `StorageType` of whatever the evaled ref `er` points at, walked from the contract's
    storage declarations (the type tree carried by the frame, independent of the opaque layout). -/
def storageTypeAt? (decls : List StorageDecl) (er : EvaledStorageRef) : Option StorageType := do
  let baseTy <- (decls.find? (fun d => d.name == er.base)).map (·.ty)
  er.steps.foldlM storageTypeStep? baseTy

/-
def storageNatResultToEval : StorageReadResult Nat -> EvalResult Nat
  | .ok n => .ok n
  | .revert => .revert
  | .error => .error .storageError

def readStorageBytesLength? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    EvalResult Nat :=
  match cfg.storage.readBytesLength er evm with
  | some result => storageNatResultToEval result
  | none => .error .storageError

/-- Bounds-check a single array index `i` against the array reached by the evaled prefix `pre`.
    Fixed arrays are checked against their declared static bound. Dynamic arrays are checked by
    asking the layout for the bare aggregate ref `layout {base, pre}` and reading the stored
    length. In both cases, an index outside `[0, length)` reverts, matching Solidity's
    `Panic(0x32)`.

    This is invoked from `evalStorageRefStep` as each `.aindex` is evaluated, so the check is
    interleaved with index evaluation exactly as solc emits it. -/
@[simp] def arrayIndexInBounds? (cfg : Config) (evm : EVM.State)
    (decls : List StorageDecl) (base : Ident) (pre : List EvaledStorageRefStep) (i : KeyValue) :
    EvalResult Unit :=
  match storageTypeAt? decls { base := base, steps := pre }, i with
  | some (.array _ n), .int iv =>
      if 0 ≤ iv ∧ iv < n then .ok () else .revert
  | some (.array _ _), _ => .error .typeError
  | some (.dynamicArray _), .int iv =>
      match cfg.storage.layout { base := base, steps := pre } evm with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int len => if 0 ≤ iv ∧ iv < len then .ok () else .revert
          | _ => .error .storageError
      | none => .error .storageError
  | some (.dynamicArray _), _ => .error .typeError
  | some (.bytes), .int iv
  | some (.string), .int iv =>
      match readStorageBytesLength? cfg evm { base := base, steps := pre } with
      | .ok len => if 0 ≤ iv ∧ iv < len then .ok () else .revert
      | .revert => .revert
      | .error e => .error e
  | some (.bytes), _ | some (.string), _ => .error .typeError
  | some _, _ => .error .typeError
  | none, _ => .error .storageError

def storagePrepareResultToEval : StorageReadResult EVM.State -> EvalResult EVM.State
  | .ok evm => .ok evm
  | .revert => .revert
  | .error => .error .storageError

def storageValueResultToEval : StorageReadResult Value -> EvalResult Value
  | .ok v => .ok v
  | .revert => .revert
  | .error => .error .storageError

mutual
/-- Recursively zero **every** storage slot occupied by a value of declared type `t` located at
    `er` — solc's `delete`.  Leaves are cleared through the opaque `layout`; the *structure* (struct
    fields, tuple/fixed-array elements, dynamic-array length + all data) is driven by `t`, so a
    nested dynamic array is cleared in full (its inner length is read and every inner element
    recursively cleared).  Mappings are skipped — their keys aren't enumerable, and solc's `delete`
    on a mapping is likewise a no-op. -/
def clearStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> EvalResult EVM.State
  | .elem _ | .contract _ =>
      match cfg.storage.layout er evm with
      | some loc => EvalResult.ofOption .storageError (storageLocStore evm loc (.int 0))
      | none => .error .storageError
  | .mapping _ _ => .ok evm
  | .struct _ fields => clearFields? cfg evm er fields
  | .tuple ts => clearTupleElems? cfg evm er 0 ts
  | .array t' n => clearArrayElems? cfg evm er t' n
  | .dynamicArray t' =>
      match cfg.storage.layout er evm with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int len =>
              match clearArrayElems? cfg evm er t' len.toNat with
              | .ok evm1 => EvalResult.ofOption .storageError (storageLocStore evm1 lenLoc (.int 0))
              | r => r
          | _ => .error .storageError
      | none => .error .storageError
  | .bytes =>
      match cfg.storage.clearValue? er .bytes evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  | .string =>
      match cfg.storage.clearValue? er .string evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  termination_by t => (sizeOf t, 0)

def clearFields? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) -> EvalResult EVM.State
  | [] => .ok evm
  | (name, ft) :: rest =>
      match clearStorage? cfg evm { er with steps := er.steps ++ [.field name] } ft with
      | .ok evm1 => clearFields? cfg evm1 er rest
      | r => r
  termination_by fields => (sizeOf fields, 0)

def clearTupleElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (k : Nat) :
    List StorageType -> EvalResult EVM.State
  | [] => .ok evm
  | tt :: rest =>
      match clearStorage? cfg evm { er with steps := er.steps ++ [.tupleElem k] } tt with
      | .ok evm1 => clearTupleElems? cfg evm1 er (k+1) rest
      | r => r
  termination_by ts => (sizeOf ts, 0)

def clearArrayElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (t' : StorageType) :
    Nat -> EvalResult EVM.State
  | 0 => .ok evm
  | n+1 =>
      match clearStorage? cfg evm { er with steps := er.steps ++ [.aindex (.int n)] } t' with
      | .ok evm1 => clearArrayElems? cfg evm1 er t' n
      | r => r
  termination_by c => (sizeOf t', c)
end

mutual
/-- Recursively write a structured `Value` into the storage of declared type `t` at `er` — the dual
    of `clearStorage?`.  Leaves go through the opaque `layout` + `storageLocStore`; structure (struct
    fields, tuple/array elements) is driven by `t`, and a `dynamicArray` target also writes its
    length.  A type/value mismatch (or a mapping/`bytes` target) is an `.error`, never a partial
    write. -/
def writeStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> Value -> EvalResult EVM.State
  | .elem _, v
  | .contract _, v =>
      match cfg.storage.layout er evm with
      | some loc => EvalResult.ofOption .storageError (storageLocStore evm loc v)
      | none => .error .storageError
  | .struct _ ftypes, .struct _ fvals => writeFields? cfg evm er ftypes fvals
  | .tuple ts, .tuple vs => writeTupleElems? cfg evm er 0 ts vs
  | .array t' n, .array vs =>
      if vs.length = n then writeArrayElems? cfg evm er t' 0 vs
      else .error .typeError
  | .dynamicArray t', .array vs => do
      -- clear the existing array first, so old elements beyond the new (possibly shorter) length
      -- don't linger — matching solc's array-assignment cleanup, and preserving the
      -- zero-beyond-length invariant that grow-only `push` relies on
      let evm0 <- clearStorage? cfg evm er (.dynamicArray t')
      let evm1 <- writeArrayElems? cfg evm0 er t' 0 vs
      let lenLoc <- EvalResult.ofOption .storageError
        (cfg.storage.layout er evm)
      EvalResult.ofOption .storageError (storageLocStore evm1 lenLoc (.int vs.length))
  | .bytes, .bytes bs =>
      match cfg.storage.writeValue? er .bytes (.bytes bs) evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  | .string, .bytes bs =>
      match cfg.storage.writeValue? er .string (.bytes bs) evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  | _, _ => .error .typeError
  termination_by t => (sizeOf t, 0)

def writeFields? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) -> List (Ident × Value) -> EvalResult EVM.State
  | [], [] => .ok evm
  | (name, ft) :: trest, (vname, fv) :: vrest =>
      if name == vname then
        match writeStorage? cfg evm { er with steps := er.steps ++ [.field name] } ft fv with
        | .ok evm1 => writeFields? cfg evm1 er trest vrest
        | r => r
      else .error .typeError
  | _, _ => .error .typeError
  termination_by ftypes => (sizeOf ftypes, 0)

def writeTupleElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (k : Nat) :
    List StorageType -> List Value -> EvalResult EVM.State
  | [], [] => .ok evm
  | tt :: trest, v :: vrest =>
      match writeStorage? cfg evm { er with steps := er.steps ++ [.tupleElem k] } tt v with
      | .ok evm1 => writeTupleElems? cfg evm1 er (k+1) trest vrest
      | r => r
  | _, _ => .error .typeError
  termination_by ts => (sizeOf ts, 0)

def writeArrayElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (t' : StorageType)
    (k : Nat) : List Value -> EvalResult EVM.State
  | [] => .ok evm
  | v :: rest =>
      match writeStorage? cfg evm { er with steps := er.steps ++ [.aindex (.int k)] } t' v with
      | .ok evm1 => writeArrayElems? cfg evm1 er t' (k+1) rest
      | r => r
  termination_by vs => (sizeOf t', sizeOf vs)
end

mutual
/-- Recursively read a value of declared type `t` out of storage at `er` into a `Value` — the read
    dual of `writeStorage?`/`clearStorage?`.  Leaves come from the opaque `layout` + `storageLocLoad`;
    structure (struct fields, tuple/fixed-array elements, dynamic-array length + all data) is driven
    by `t`, so a nested dynamic array is read in full.  A mapping has no enumerable contents, so a
    whole-mapping read is an `.error`. -/
def readStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> EvalResult Value
  | .elem _
  | .contract _ =>
      match cfg.storage.layout er evm with
      | some loc => .ok (storageLocLoad evm loc)
      | none => .error .storageError
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let fvals <- readFields? cfg evm er fields
      pure (.struct name fvals)
  | .tuple ts => do
      let vs <- readTupleElems? cfg evm er 0 ts
      pure (.tuple vs)
  | .array t' n => do
      let vs <- readArrayElems? cfg evm er t' 0 n
      pure (.array vs)
  | .dynamicArray t' =>
      match cfg.storage.layout er evm with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int len => do
              let vs <- readArrayElems? cfg evm er t' 0 len.toNat
              pure (.array vs)
          | _ => .error .storageError
      | none => .error .storageError
  | .bytes =>
      match cfg.storage.readValue? er .bytes evm with
      | some result => storageValueResultToEval result
      | none => .error .storageError
  | .string =>
      match cfg.storage.readValue? er .string evm with
      | some result => storageValueResultToEval result
      | none => .error .storageError
  termination_by t => (sizeOf t, 0)

def readFields? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) -> EvalResult (List (Ident × Value))
  | [] => .ok []
  | (name, ft) :: rest => do
      let v <- readStorage? cfg evm { er with steps := er.steps ++ [.field name] } ft
      let vrest <- readFields? cfg evm er rest
      pure ((name, v) :: vrest)
  termination_by fields => (sizeOf fields, 0)

def readTupleElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (k : Nat) :
    List StorageType -> EvalResult (List Value)
  | [] => .ok []
  | tt :: rest => do
      let v <- readStorage? cfg evm { er with steps := er.steps ++ [.tupleElem k] } tt
      let vrest <- readTupleElems? cfg evm er (k+1) rest
      pure (v :: vrest)
  termination_by ts => (sizeOf ts, 0)

def readArrayElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (t' : StorageType)
    (k : Nat) : Nat -> EvalResult (List Value)
  | 0 => .ok []
  | c+1 => do
      let v <- readStorage? cfg evm { er with steps := er.steps ++ [.aindex (.int k)] } t'
      let vrest <- readArrayElems? cfg evm er t' (k+1) c
      pure (v :: vrest)
  termination_by c => (sizeOf t', c)
end

def readStorageArrayLength? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef)
    : StorageType -> EvalResult Value
  | .array _ n => pure (.int n)
  | .elem (.bytes n) => pure (.int (fixedBytesSize n))
  | .dynamicArray _ =>
      match cfg.storage.layout er evm with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int n => pure (.int n)
          | _ => .error .storageError
      | none => .error .storageError
  | .bytes | .string => do
      let len <- readStorageBytesLength? cfg evm er
      pure (.int len)
  | _ => .error .typeError

-/
mutual
def defaultValue? : StorageType -> EvalResult Value
  | .elem (.bool) => pure (.bool false)
  | .elem (.address) => pure (.address (.ofNat 0))
  | .elem (.bytes n) => pure (.fixedBytes n (List.replicate (n.val + 1) 0))
  | .elem _ => pure (.int 0)
  | .contract _ => pure (.address (.ofNat 0))
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let values <- defaultFields? fields
      pure (.struct name values)
  | .tuple ts => do
      let values <- defaultValues? ts
      pure (.tuple values)
  | .array elemTy n => do
      let value <- defaultValue? elemTy
      pure (.array (List.replicate n value))
  | .dynamicArray _ => pure (.array [])
  | .bytes | .string => pure (.bytes ByteArray.empty)
  termination_by t => (sizeOf t, 0)

def defaultFields? : List (Ident × StorageType) -> EvalResult (List (Ident × Value))
  | [] => pure []
  | (name, ty) :: rest => do
      let value <- defaultValue? ty
      let values <- defaultFields? rest
      pure ((name, value) :: values)
  termination_by fields => (sizeOf fields, 0)

def defaultValues? : List StorageType -> EvalResult (List Value)
  | [] => pure []
  | ty :: rest => do
      let value <- defaultValue? ty
      let values <- defaultValues? rest
      pure (value :: values)
  termination_by ts => (sizeOf ts, 0)
end

/-
/-! ## Operation-owned storage backends

The definitions above are the compatibility implementation for the historical slot layout.  New
semantics enter through `configuredStorageBackend`; the adapter below is the only place where the
generic executor falls back to interpreting `StorageLoc`s. -/

private def storageOnlyExternalABI : ExternalCallABI where
  encode? := fun _ _ => none
  decode? := fun _ _ => none

private def storageOnlyConfig (layout : StorageLayout) : Config :=
  { storage := layout
    externalABI := storageOnlyExternalABI
    selfDeployment := fun _ _ => none }

def legacyPushStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef)
    (ty : StorageType) (value : Option Value) : EvalResult EVM.State :=
  match ty with
  | .dynamicArray elemTy => do
      let lenLoc <- EvalResult.ofOption .storageError
        (cfg.storage.layout er evm)
      match storageLocLoad evm lenLoc with
      | .int len => do
          let evmLen <- EvalResult.ofOption .storageError
            (storageLocStore evm lenLoc (.int (len + 1)))
          match value with
          | some v =>
              writeStorage? cfg evmLen
                { er with steps := er.steps ++ [.aindex (.int len)] } elemTy v
          | none => pure evmLen
      | _ => .error .storageError
  | .bytes | .string => do
      match (← readStorage? cfg evm er ty) with
      | .bytes ba =>
          match value with
          | none => writeStorage? cfg evm er ty (.bytes (ba.push 0))
          | some (.fixedBytes n bs) =>
              if n.val = 0 ∧ bs.length = 1 then
                writeStorage? cfg evm er ty (.bytes (ba ++ ByteArray.mk bs.toArray))
              else .error .typeError
          | some _ => .error .typeError
      | _ => .error .storageError
  | _ => .error .storageError

def legacyPopStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef)
    (ty : StorageType) : EvalResult EVM.State :=
  match ty with
  | .dynamicArray elemTy => do
      let lenLoc <- EvalResult.ofOption .storageError
        (cfg.storage.layout er evm)
      match storageLocLoad evm lenLoc with
      | .int len =>
          if len ≤ 0 then .revert
          else do
            let evm1 <- clearStorage? cfg evm
              { er with steps := er.steps ++ [.aindex (.int (len - 1))] } elemTy
            EvalResult.ofOption .storageError
              (storageLocStore evm1 lenLoc (.int (len - 1)))
      | _ => .error .storageError
  | .bytes | .string => do
      match (← readStorage? cfg evm er ty) with
      | .bytes ba =>
          if ba.size = 0 then .revert
          else writeStorage? cfg evm er ty (.bytes (ba.extract 0 (ba.size - 1)))
      | _ => .error .storageError
  | _ => .error .storageError

@[simp] def legacyStorageLength? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef)
    (ty : StorageType) : EvalResult Nat := do
  match ← readStorageArrayLength? cfg evm er ty with
  | .int n => if n < 0 then .error .storageError else pure n.toNat
  | _ => .error .storageError

/-- Wrap a historical slot layout as a complete executable backend. -/
def StorageLayout.toBackend (layout : StorageLayout) : StorageBackend :=
  let cfg := storageOnlyConfig layout
  { read := fun er ty evm => readStorage? cfg evm er ty
    write := fun er ty value evm =>
      match value with
      | .struct _ _ | .array _ | .bytes _ => writeStorage? cfg evm er ty value
      | _ => do
          let loc <- EvalResult.ofOption .storageError (layout.layout er evm)
          EvalResult.ofOption .storageError (storageLocStore evm loc value)
    clear := fun er ty evm => clearStorage? cfg evm er ty
    length := fun er ty evm => legacyStorageLength? cfg evm er ty
    push := fun er ty value evm => legacyPushStorage? cfg evm er ty value
    pop := fun er ty evm => legacyPopStorage? cfg evm er ty
    locate? := layout.layout }

@[simp] theorem StorageLayout.toBackend_read_elem (layout : StorageLayout)
    (er : EvaledStorageRef) (ty : ElemType) (evm : EVM.State) (loc : StorageLoc)
    (hloc : layout.layout er evm = some loc) :
    layout.toBackend.read er (.elem ty) evm = .ok (storageLocLoad evm loc) := by
  simp [StorageLayout.toBackend, storageOnlyConfig, readStorage?, hloc]

@[simp] theorem StorageLayout.toBackend_write_scalar (layout : StorageLayout)
    (er : EvaledStorageRef) (ty : StorageType) (value : Value)
    (evm evm' : EVM.State) (loc : StorageLoc)
    (hloc : layout.layout er evm = some loc)
    (hscalar : match value with | .struct _ _ | .array _ | .bytes _ => False | _ => True)
    (hstore : storageLocStore evm loc value = some evm') :
    layout.toBackend.write er ty value evm = .ok evm' := by
  cases value <;>
    simp_all [StorageLayout.toBackend, EvalResult.ofOption, EvalResult.bind, bind]

/-- Compatibility backend retaining the original `Config` definitionally. This makes the staged
    path transparent to existing proofs while `StorageLayout.toBackend` remains available to new
    generated configurations. -/
def Config.legacyStorageBackend (cfg : Config) : StorageBackend :=
  { read := fun er ty evm => readStorage? cfg evm er ty
    write := fun er ty value evm =>
      match value with
      | .struct _ _ | .array _ | .bytes _ => writeStorage? cfg evm er ty value
      | _ => do
          let loc <- EvalResult.ofOption .storageError (cfg.storage.layout er evm)
          EvalResult.ofOption .storageError (storageLocStore evm loc value)
    clear := fun er ty evm => clearStorage? cfg evm er ty
    length := fun er ty evm => legacyStorageLength? cfg evm er ty
    push := fun er ty value evm => legacyPushStorage? cfg evm er ty value
    pop := fun er ty evm => legacyPopStorage? cfg evm er ty
    locate? := cfg.storage.layout }

/-- Select explicitly configured behavior, or the staged compatibility adapter. -/
abbrev configuredStorageBackend (cfg : Config) : StorageBackend :=
  cfg.storageBackend?.getD cfg.legacyStorageBackend

@[inline] abbrev backendReadStorage? (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) : EvalResult Value :=
  (configuredStorageBackend cfg).read er ty evm

@[inline] abbrev backendWriteStorage? (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) (value : Value) : EvalResult EVM.State :=
  (configuredStorageBackend cfg).write er ty value evm

@[inline] abbrev backendClearStorage? (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) : EvalResult EVM.State :=
  (configuredStorageBackend cfg).clear er ty evm

@[inline] abbrev backendStorageLength? (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) : EvalResult Nat :=
  (configuredStorageBackend cfg).length er ty evm

@[inline] abbrev backendPushStorage? (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) (value : Option Value) : EvalResult EVM.State :=
  (configuredStorageBackend cfg).push er ty value evm

@[inline] abbrev backendPopStorage? (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) : EvalResult EVM.State :=
  (configuredStorageBackend cfg).pop er ty evm

/-- Dispatch equations keep old proof scripts transparent: once a concrete legacy config is
    unfolded, `none` reduces directly to the historical implementation. -/
@[simp] theorem backendReadStorage?_eq (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) :
    backendReadStorage? cfg evm er ty =
      match cfg.storageBackend? with
      | some backend => backend.read er ty evm
      | none => readStorage? cfg evm er ty := by
  cases h : cfg.storageBackend? <;>
    simp [backendReadStorage?, configuredStorageBackend, h, Config.legacyStorageBackend]

@[simp] theorem backendWriteStorage?_eq (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) (value : Value) :
    backendWriteStorage? cfg evm er ty value =
      (match cfg.storageBackend? with
      | some backend => backend.write er ty value evm
      | none =>
          match value with
          | .struct _ _ | .array _ | .bytes _ => writeStorage? cfg evm er ty value
          | _ => do
              let loc <- EvalResult.ofOption .storageError (cfg.storage.layout er evm)
              EvalResult.ofOption .storageError (storageLocStore evm loc value)) := by
  cases h : cfg.storageBackend? <;>
    simp [backendWriteStorage?, configuredStorageBackend, h, Config.legacyStorageBackend]

@[simp] theorem backendClearStorage?_eq (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) :
    backendClearStorage? cfg evm er ty =
      match cfg.storageBackend? with
      | some backend => backend.clear er ty evm
      | none => clearStorage? cfg evm er ty := by
  cases h : cfg.storageBackend? <;>
    simp [backendClearStorage?, configuredStorageBackend, h, Config.legacyStorageBackend]

@[simp] theorem backendStorageLength?_eq (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) :
    backendStorageLength? cfg evm er ty =
      match cfg.storageBackend? with
      | some backend => backend.length er ty evm
      | none => legacyStorageLength? cfg evm er ty := by
  cases h : cfg.storageBackend? <;>
    simp [backendStorageLength?, configuredStorageBackend, h, Config.legacyStorageBackend]

@[simp] theorem backendPushStorage?_eq (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) (value : Option Value) :
    backendPushStorage? cfg evm er ty value =
      match cfg.storageBackend? with
      | some backend => backend.push er ty value evm
      | none => legacyPushStorage? cfg evm er ty value := by
  cases h : cfg.storageBackend? <;>
    simp [backendPushStorage?, configuredStorageBackend, h, Config.legacyStorageBackend]

@[simp] theorem backendPopStorage?_eq (cfg : Config) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) :
    backendPopStorage? cfg evm er ty =
      match cfg.storageBackend? with
      | some backend => backend.pop er ty evm
      | none => legacyPopStorage? cfg evm er ty := by
  cases h : cfg.storageBackend? <;>
    simp [backendPopStorage?, configuredStorageBackend, h, Config.legacyStorageBackend]

@[simp] theorem backendReadStorage?_of_none {cfg : Config} (h : cfg.storageBackend? = none)
    (evm : EVM.State) (er : EvaledStorageRef) (ty : StorageType) :
    backendReadStorage? cfg evm er ty = readStorage? cfg evm er ty := by
  simp [backendReadStorage?, configuredStorageBackend, h, Config.legacyStorageBackend]

@[simp] theorem backendWriteStorage?_aggregate_of_none {cfg : Config}
    (h : cfg.storageBackend? = none) (evm : EVM.State) (er : EvaledStorageRef)
    (ty : StorageType) (value : Value)
    (haggregate : match value with | .struct _ _ | .array _ | .bytes _ => True | _ => False) :
    backendWriteStorage? cfg evm er ty value = writeStorage? cfg evm er ty value := by
  unfold backendWriteStorage? configuredStorageBackend
  simp only [h, Option.getD_none, Config.legacyStorageBackend]
  cases value <;> simp_all

@[simp] theorem backendClearStorage?_of_none {cfg : Config} (h : cfg.storageBackend? = none)
    (evm : EVM.State) (er : EvaledStorageRef) (ty : StorageType) :
    backendClearStorage? cfg evm er ty = clearStorage? cfg evm er ty := by
  simp [backendClearStorage?, configuredStorageBackend, h, Config.legacyStorageBackend]

@[simp] theorem backendStorageLength?_of_none {cfg : Config}
    (h : cfg.storageBackend? = none) (evm : EVM.State) (er : EvaledStorageRef)
    (ty : StorageType) :
    backendStorageLength? cfg evm er ty = legacyStorageLength? cfg evm er ty := by
  simp [backendStorageLength?, configuredStorageBackend, h, Config.legacyStorageBackend]

theorem backendReadStorage?_elem {cfg : Config} {evm : EVM.State}
    {er : EvaledStorageRef} {ty : ElemType} {loc : StorageLoc}
    (hloc : cfg.storage.layout er evm = some loc) :
    backendReadStorage? cfg evm er (.elem ty) = .ok (storageLocLoad evm loc) := by
  unfold backendReadStorage? configuredStorageBackend
  cases hbackend : cfg.storageBackend? with
  | none =>
      simp [Config.legacyStorageBackend, readStorage?, hloc]
  | some backend =>
      simpa [hbackend] using
        cfg.storageBackend_read_scalar backend er ty evm loc hbackend hloc

theorem backendWriteStorage?_scalar {cfg : Config} {evm evm' : EVM.State}
    {er : EvaledStorageRef} {ty : StorageType} {value : Value} {loc : StorageLoc}
    (hloc : cfg.storage.layout er evm = some loc)
    (hscalar : match value with | .struct _ _ | .array _ | .bytes _ => False | _ => True)
    (hstore : storageLocStore evm loc value = some evm') :
    backendWriteStorage? cfg evm er ty value = .ok evm' := by
  unfold backendWriteStorage? configuredStorageBackend
  cases hbackend : cfg.storageBackend? with
  | none =>
      simp only [Option.getD_none, Config.legacyStorageBackend]
      cases value <;> simp_all [EvalResult.ofOption, EvalResult.bind, bind]
  | some backend =>
      simpa [hbackend] using
        cfg.storageBackend_write_scalar backend er ty value evm evm' loc hbackend hloc hscalar hstore

private def backendArrayIndexInBoundsWith? (backend : StorageBackend) (evm : EVM.State)
    (decls : List StorageDecl) (base : Ident) (pre : List EvaledStorageRefStep)
    (i : KeyValue) : EvalResult Unit :=
  match storageTypeAt? decls { base := base, steps := pre }, i with
  | some (.array _ n), .int iv =>
      if 0 ≤ iv ∧ iv < n then .ok () else .revert
  | some (.array _ _), _ => .error .typeError
  | some ty@(.dynamicArray _), .int iv
  | some ty@(.bytes), .int iv
  | some ty@(.string), .int iv =>
      match backend.length { base := base, steps := pre } ty evm with
      | .ok len => if 0 ≤ iv ∧ iv < len then .ok () else .revert
      | .revert => .revert
      | .error e => .error e
  | some (.dynamicArray _), _ | some (.bytes), _ | some (.string), _ => .error .typeError
  | some _, _ => .error .typeError
  | none, _ => .error .storageError

/-- Bounds checks use backend-owned lengths when a backend is configured. The legacy branch is
    definitionally the historical checker so existing slot-layout proofs remain source-compatible. -/
@[simp] def backendArrayIndexInBounds? (cfg : Config) (evm : EVM.State)
    (decls : List StorageDecl) (base : Ident) (pre : List EvaledStorageRefStep)
    (i : KeyValue) : EvalResult Unit :=
  match cfg.storageBackend? with
  | some backend => backendArrayIndexInBoundsWith? backend evm decls base pre i
  | none => arrayIndexInBounds? cfg evm decls base pre i

-/

end Solm
