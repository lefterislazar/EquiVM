import Solm.Storage
import Solm.Value
import ABI.Decode

/-! Shared execution context: external-call ABI, configuration, and frames. -/

namespace Solm

open ABI

structure ExternalCallABI where
  encode? : Ident -> List Value -> Option EVM.Bytes
  decode? : Ident -> EVM.Bytes-> Option (List Value)

structure Config where
  storage : StorageLayout
  /-- Executable storage behavior. `none` selects the compatibility adapter for `storage`; new
      configurations should provide a backend explicitly. -/
  storageBackend? : Option StorageBackend := none
  /-- Compatibility contract for proof-oriented scalar location lemmas. Vacuous for the staged
      legacy path; an explicit backend must justify any `locate` oracle it exposes through
      `storage`. -/
  storageBackend_read_scalar : ∀ backend er ty evm loc,
    storageBackend? = some backend ->
    storage.layout er evm = some loc ->
    backend.read er (.elem ty) evm = .ok (storageLocLoad evm loc) := by
      intros backend _ _ _ _ h
      simp at h
  storageBackend_write_scalar : ∀ backend er ty value evm evm' loc,
    storageBackend? = some backend ->
    storage.layout er evm = some loc ->
    (match value with | .struct _ _ | .array _ | .bytes _ => False | _ => True) ->
    storageLocStore evm loc value = some evm' ->
    backend.write er ty value evm = .ok evm' := by
      intros backend _ _ _ _ _ _ h
      simp at h
  externalABI : ExternalCallABI
  abiDecodeMode : ABI.DecodeMode := ABI.DecodeMode.modern
  /-- Initialisation code (creation bytecode ++ ABI-encoded constructor args) for a
      `new` of the named contract. -/
  creationCode : Ident -> List Value -> Option EVM.Bytes := fun _ _ => none

  /-- Scheme for initialisation code (creation bytecode ++ ABI-encoded constructor args) for
      deployment of the contract's constructor -/
  selfDeployment : EVM.Bytes → List Value → Option EVM.Bytes

structure Frame where
  contract : ContractDecl
  locals : Store

end Solm
