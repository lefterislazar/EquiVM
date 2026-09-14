import Benchmarks.Dss.End.Spec

/-!
# Trusted concrete selector facts for DSS End

Lean cannot evaluate the keccak FFI in kernel-normalized proofs, so the usual
`keccak(signature)[0:4]` function selector literals are recorded here as the
narrow trusted base allowed by the benchmark instructions.
-/

namespace Benchmarks.Dss.End

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom endWardsSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr wardsTransition))).extract 0 4
      = ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom endVatSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr vatTransition))).extract 0 4
      = ⟨#[0x36, 0x56, 0x9e, 0x77]⟩

/-- `keccak("cat()")[0:4] = 0xe4881813`. -/
axiom endCatSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr catTransition))).extract 0 4
      = ⟨#[0xe4, 0x88, 0x18, 0x13]⟩

/-- `keccak("dog()")[0:4] = 0xc3b3ad7f`. -/
axiom endDogSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr dogTransition))).extract 0 4
      = ⟨#[0xc3, 0xb3, 0xad, 0x7f]⟩

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
axiom endVowSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr vowTransition))).extract 0 4
      = ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩

/-- `keccak("pot()")[0:4] = 0x4ba2363a`. -/
axiom endPotSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr potTransition))).extract 0 4
      = ⟨#[0x4b, 0xa2, 0x36, 0x3a]⟩

/-- `keccak("spot()")[0:4] = 0x6f265b93`. -/
axiom endSpotSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr spotTransition))).extract 0 4
      = ⟨#[0x6f, 0x26, 0x5b, 0x93]⟩

/-- `keccak("cure()")[0:4] = 0x840782ed`. -/
axiom endCureSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr cureTransition))).extract 0 4
      = ⟨#[0x84, 0x07, 0x82, 0xed]⟩

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom endLiveSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr liveTransition))).extract 0 4
      = ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩

/-- `keccak("when()")[0:4] = 0xe2b0caef`. -/
axiom endWhenSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr whenTransition))).extract 0 4
      = ⟨#[0xe2, 0xb0, 0xca, 0xef]⟩

/-- `keccak("wait()")[0:4] = 0x64bd7013`. -/
axiom endWaitSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr waitTransition))).extract 0 4
      = ⟨#[0x64, 0xbd, 0x70, 0x13]⟩

/-- `keccak("debt()")[0:4] = 0x0dca59c1`. -/
axiom endDebtSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr debtTransition))).extract 0 4
      = ⟨#[0x0d, 0xca, 0x59, 0xc1]⟩

/-- `keccak("tag(bytes32)")[0:4] = 0xee6447b5`. -/
axiom endTagSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr tagTransition))).extract 0 4
      = ⟨#[0xee, 0x64, 0x47, 0xb5]⟩

/-- `keccak("gap(bytes32)")[0:4] = 0xe6ee62aa`. -/
axiom endGapSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr gapTransition))).extract 0 4
      = ⟨#[0xe6, 0xee, 0x62, 0xaa]⟩

/-- `keccak("Art(bytes32)")[0:4] = 0xe1340a3d`. -/
axiom endArtSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr ArtTransition))).extract 0 4
      = ⟨#[0xe1, 0x34, 0x0a, 0x3d]⟩

/-- `keccak("fix(bytes32)")[0:4] = 0x63fad85e`. -/
axiom endFixSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fixTransition))).extract 0 4
      = ⟨#[0x63, 0xfa, 0xd8, 0x5e]⟩

/-- `keccak("bag(address)")[0:4] = 0x9255f809`. -/
axiom endBagSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr bagTransition))).extract 0 4
      = ⟨#[0x92, 0x55, 0xf8, 0x09]⟩

/-- `keccak("out(bytes32,address)")[0:4] = 0xc939ebfc`. -/
axiom endOutSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr outTransition))).extract 0 4
      = ⟨#[0xc9, 0x39, 0xeb, 0xfc]⟩

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom endRelySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr relyTransition))).extract 0 4
      = ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom endDenySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr denyTransition))).extract 0 4
      = ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom endFileAddressSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fileAddressTransition))).extract 0 4
      = ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom endFileUintSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fileUintTransition))).extract 0 4
      = ⟨#[0x29, 0xae, 0x81, 0x14]⟩

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom endCageSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr cageTransition))).extract 0 4
      = ⟨#[0x69, 0x24, 0x50, 0x09]⟩

/-- `keccak("cage(bytes32)")[0:4] = 0xe2702fdc`. -/
axiom endCageIlkSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr cageIlkTransition))).extract 0 4
      = ⟨#[0xe2, 0x70, 0x2f, 0xdc]⟩

/-- `keccak("snip(bytes32,uint256)")[0:4] = 0x38c6de40`. -/
axiom endSnipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr snipTransition))).extract 0 4
      = ⟨#[0x38, 0xc6, 0xde, 0x40]⟩

/-- `keccak("skip(bytes32,uint256)")[0:4] = 0x503ecf06`. -/
axiom endSkipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr skipTransition))).extract 0 4
      = ⟨#[0x50, 0x3e, 0xcf, 0x06]⟩

/-- `keccak("skim(bytes32,address)")[0:4] = 0x89ea45d3`. -/
axiom endSkimSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr skimTransition))).extract 0 4
      = ⟨#[0x89, 0xea, 0x45, 0xd3]⟩

/-- `keccak("free(bytes32)")[0:4] = 0xc83062c6`. -/
axiom endFreeSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr freeTransition))).extract 0 4
      = ⟨#[0xc8, 0x30, 0x62, 0xc6]⟩

/-- `keccak("thaw()")[0:4] = 0x5920375c`. -/
axiom endThawSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr thawTransition))).extract 0 4
      = ⟨#[0x59, 0x20, 0x37, 0x5c]⟩

/-- `keccak("flow(bytes32)")[0:4] = 0x4a10eaa6`. -/
axiom endFlowSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr flowTransition))).extract 0 4
      = ⟨#[0x4a, 0x10, 0xea, 0xa6]⟩

/-- `keccak("pack(uint256)")[0:4] = 0x6ea42555`. -/
axiom endPackSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr packTransition))).extract 0 4
      = ⟨#[0x6e, 0xa4, 0x25, 0x55]⟩

/-- `keccak("cash(bytes32,uint256)")[0:4] = 0xfe8507c6`. -/
axiom endCashSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr cashTransition))).extract 0 4
      = ⟨#[0xfe, 0x85, 0x07, 0xc6]⟩

end Benchmarks.Dss.End
