import Lean
import Solm.SolidityLayout
import Solm.Semantics.StorageOps

/-!
# Compile-time Solidity storage generation

The elaborators below evaluate the closed storage declarations while elaborating the spec.  They
validate supported types and precompute every top-level slot/offset, emitting a direct match on the
storage variable name. Nested paths retain only the arithmetic that necessarily depends on runtime
mapping keys, array indices, or the current short/long bytes representation.
-/

namespace Solm
open ABI
open Lean Elab Term Meta

namespace MetaSolidityLayout

private structure BaseAllocation where
  name : Ident
  slot : Nat
  offset : Nat
  size : Nat

private def supportedKeyType : ElemType -> Bool
  | .bool | .address | .int _ | .bytes _ => true
  | .fixed _ | .function => false

mutual
private def supportedStorageType : StorageType -> Bool
  | .elem (.fixed _) | .elem .function => false
  | .elem _ | .contract _ | .bytes | .string => true
  | .mapping key value => supportedKeyType key && supportedStorageType value
  | .struct _ fields => supportedStorageFields fields
  | .tuple _ => false
  | .array elem _ | .dynamicArray elem => supportedStorageType elem

private def supportedStorageFields : List (Ident × StorageType) -> Bool
  | [] => true
  | field :: rest => supportedStorageType field.2 && supportedStorageFields rest
end

private def typeSize? (structs : List StructDecl) (ty : StorageType) : Option Nat := do
  let (size, _) <- slotTypeSolidityStorageNode structs ty
  pure size

private def allocateBases (structs : List StructDecl) :
    List StorageDecl -> Nat -> Nat -> Option (List BaseAllocation)
  | [], _, _ => some []
  | decl :: rest, slot, offset => do
      if !supportedStorageType decl.ty then none else pure ()
      let size <- typeSize? structs decl.ty
      let packable := solidityTypeIsPackable decl.ty
      let crosses := offset + size > 32
      let startSlot := if packable then (if crosses then slot + 1 else slot)
                       else (if offset = 0 then slot else slot + 1)
      let startOffset := if packable && !crosses then offset else 0
      let endOffset := startOffset + size
      let words := (size + 31) / 32
      let nextSlot := if packable then (if endOffset = 32 then startSlot + 1 else startSlot)
                      else startSlot + words
      let nextOffset := if packable && endOffset < 32 then endOffset else 0
      let tail <- allocateBases structs rest nextSlot nextOffset
      pure ({ name := decl.name, slot := startSlot, offset := startOffset, size := size } :: tail)

private unsafe def evalClosedTerm (alpha : Type) (typeStx valueStx : Term) : TermElabM alpha := do
  let type <- elabType typeStx
  let value <- elabTermEnsuringType valueStx type
  evalExpr alpha type value

private def natTerm (n : Nat) : Term := Syntax.mkNumLit (toString n)
private def stringTerm (s : String) : Term := Syntax.mkStrLit s

private def allocationTerm (a : BaseAllocation) : TermElabM Term :=
  `(term|
    ({ slot := Ethereum.UInt256.ofNat $(natTerm a.slot)
       offset := (Fin.ofNat 32 $(natTerm a.offset))
       size := $(natTerm a.size)
       bitOffset := none } : IntermediateStorageLoc))

private def generatedRawLayout
    (structsStx declsStx : Term)
    (allocations : List BaseAllocation) : TermElabM Term := do
  let refName := mkIdent (← mkFreshUserName `ref)
  let evmName := mkIdent (← mkFreshUserName `evm)
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for a in allocations do
    let loc <- allocationTerm a
    let name := stringTerm a.name
    let body <- `(term|
      match (($declsStx).find? (fun decl : StorageDecl => decl.name == $name)) with
      | some decl => followSolidityType $structsStx $evmName $loc ($refName).steps decl.ty
      | none => none)
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $name => $body))
  alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => none))
  let body <- `(term| match ($refName).base with $alts:matchAlt*)
  `(term|
    ((fun $refName:ident $evmName:ident => $body) :
      EvaledStorageRef -> EVM.State -> Option StorageLoc))

private def elaborateLayout (structsStx declsStx : Term) : TermElabM Term := do
  let structs <- unsafe evalClosedTerm (List StructDecl) (← `(term| List StructDecl)) structsStx
  let decls <- unsafe evalClosedTerm (List StorageDecl) (← `(term| List StorageDecl)) declsStx
  let names := decls.map (·.name)
  unless names.eraseDups.length = names.length do
    throwError "duplicate Solidity storage declaration name"
  let some allocations := allocateBases structs decls 0 0
    | throwError "unsupported Solidity persistent-storage type or invalid layout"
  let raw <- generatedRawLayout structsStx declsStx allocations
  `(term| solidityStorageLayout $raw)

elab "solidityLayout! " "[" structs:term "]" "[" decls:term "]" : term => do
  let stx <- elaborateLayout structs decls
  elabTerm stx none

macro "solidityStorage! " "[" structs:term "]" "[" decls:term "]" : term =>
  `((solidityLayout! [$structs] [$decls]).toBackend)

end MetaSolidityLayout
end Solm
