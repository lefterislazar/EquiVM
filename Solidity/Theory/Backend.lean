import Solidity.Semantics
import Reasoning.Storage
import Solidity.Theory.Slots

/-!
# Storage facts

The semantics reads and writes storage with the algorithms of `Solidity.Storage` over
`cfg.storageLayout`.  `Config.Leaf cfg er loc` says they treat `er` as the scalar at location
`loc`, which holds whenever the layout maps `er` to `.leaf loc` (`Config.leaf_of_locate`).  The
scalar lemmas of `Body.lean` are stated on it.  For dynamically-sized values the lemmas take the
results of `Storage.length`, `push`, `pop` and `clear` as hypotheses; their values at a header
slot (`.anchor`) are below.
-/

namespace Solidity

open Ethereum Reasoning.Theory

/-- Storage reads and writes the scalar `er` at `loc`. -/
structure Config.Leaf (cfg : Config) (er : Solm.EvaledStorageRef) (loc : Solm.StorageLoc) : Prop where
  read : ∀ (e : ABI.ElemType) (evm : EVM.State),
    Storage.read cfg.storageLayout er (.elem e) evm = .ok (Solm.storageLocLoad evm loc)
  write : ∀ (e : ABI.ElemType) (v : Solm.Value) (evm evm' : EVM.State),
    Solm.storageLocStore evm loc v = some evm' → Storage.write cfg.storageLayout er (.elem e) v evm = .ok evm'
  /-- `delete` of a scalar writes the integer zero at its location. -/
  clear : ∀ (e : ABI.ElemType) (evm evm' : EVM.State),
    Solm.storageLocStore evm loc (.int 0) = some evm' → Storage.clear cfg.storageLayout er (.elem e) evm = .ok evm'

/-- A layout that maps `er` to the leaf `loc`. -/
theorem Config.leaf_of_locate {cfg : Config} {L : Solm.StorageLayout} {er : Solm.EvaledStorageRef}
    {loc : Solm.StorageLoc} (hL : cfg.storageLayout = L) (hl : L er = some (.leaf loc)) : cfg.Leaf er loc :=
  ⟨fun e evm => by rw [hL]; exact Storage.read_elem hl e evm,
   fun e _ _ _ hst => by rw [hL]; exact Storage.write_elem hl e hst,
   fun e _ _ hst => by rw [hL]; exact Storage.clear_elem hl e hst⟩

/-- Storing the integer zero at a location is storing `false` or the zero address there (all are
    the zero word). -/
theorem storageLocStore_int_zero_eq_bool_false (evm : EVM.State) (loc : Solm.StorageLoc) :
    Solm.storageLocStore evm loc (.int 0) = Solm.storageLocStore evm loc (.bool false) := by
  unfold Solm.storageLocStore
  rfl

theorem storageLocStore_int_zero_eq_address_zero (evm : EVM.State) (loc : Solm.StorageLoc) :
    Solm.storageLocStore evm loc (.int 0) = Solm.storageLocStore evm loc (.address (AccountAddress.ofNat 0)) := by
  unfold Solm.storageLocStore
  rfl

/-- A leaf of a config built from a layout table (`defaultConfig`). -/
theorem Config.leaf_of_table {cfg : Config} {t : LayoutTable} {er : Solm.EvaledStorageRef} {loc : Solm.StorageLoc}
    (hb : cfg.storageLayout = Solidity.storageLayout t) (hl : layout t er = some (.leaf loc)) : cfg.Leaf er loc :=
  Config.leaf_of_locate hb hl

/-! ## Storage types of the value types -/

@[simp] theorem storageTypeOf_uint (env : TypeEnv) (w : ABI.BitWidth) :
    storageTypeOf env (.uint w) = some (.elem (.int (.uint w))) := rfl
@[simp] theorem storageTypeOf_int (env : TypeEnv) (w : ABI.BitWidth) :
    storageTypeOf env (.int w) = some (.elem (.int (.sint w))) := rfl
@[simp] theorem storageTypeOf_bool (env : TypeEnv) : storageTypeOf env .bool = some (.elem .bool) := rfl
@[simp] theorem storageTypeOf_address (env : TypeEnv) (p : Bool) :
    storageTypeOf env (.address p) = some (.elem .address) := rfl
@[simp] theorem storageTypeOf_fixedBytes (env : TypeEnv) (n : Fin 32) :
    storageTypeOf env (.fixedBytes n) = some (.elem (.bytes n)) := rfl
@[simp] theorem storageTypeOf_bytes (env : TypeEnv) : storageTypeOf env .bytes = some .bytes := rfl
@[simp] theorem storageTypeOf_string (env : TypeEnv) : storageTypeOf env .string = some .string := rfl

/-! ## Lengths and pushes at a header slot -/

/-- The length of a dynamic array whose header is at `slot`: the slot word. -/
theorem solidity_length_dynArray {L : Solm.StorageLayout} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : L er = some (.anchor slot)) (st : Solm.StorageType) (evm : EVM.State) :
    Storage.length L er (.dynamicArray st) evm =
      .ok (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat := by
  show Solm.solidityStorageLength? L er (.dynamicArray st) evm = _
  simp only [Solm.solidityStorageLength?, Solm.solidityDynamicLength?, Solm.solidityLengthLoc?,
    Solm.solidityAnchor?_of_anchor hl, Option.map_some, Solm.EvalResult.ofOption, bind, Solm.EvalResult.bind]
  rw [show Solm.solidityAnchorWordLoc slot = uint256Loc slot from rfl, storageLocLoad_uint256]
  simp

/-- A static array's length is its declared length. -/
theorem solidity_length_array (L : Solm.StorageLayout) (er : Solm.EvaledStorageRef) (st : Solm.StorageType) (n : Nat)
    (evm : EVM.State) : Storage.length L er (.array st n) evm = .ok n := rfl

/-- `push()` on a dynamic array whose header is at `slot`: the length word is incremented. -/
theorem solidity_push_none {L : Solm.StorageLayout} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : L er = some (.anchor slot)) (st : Solm.StorageType) (evm : EVM.State) :
    Storage.push L er (.dynamicArray st) none evm =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (EVM.wordOfInt ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat + 1))) := by
  rw [Storage.push_dynArray_none_eq_solm]
  show Solm.solidityPushStorage? L er (.dynamicArray st) none evm = _
  simp only [Solm.solidityPushStorage?, Solm.solidityDynamicLength?, Solm.solidityLengthLoc?,
    Solm.solidityAnchor?_of_anchor hl, Option.map_some, Solm.EvalResult.ofOption, bind, Solm.EvalResult.bind]
  rw [show Solm.solidityAnchorWordLoc slot = uint256Loc slot from rfl, storageLocLoad_uint256]
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
  rw [if_neg (not_lt.mpr (Int.natCast_nonneg _))]
  simp only [storageLocStore_uint256_int]

end Solidity
