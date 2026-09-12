import Benchmarks.Dss.Flapper.Spec
import Reasoning.Dispatch

/-!
# Trusted selector facts for DSS Flapper

These are the accepted concrete ABI selector facts:
`keccak(signature)[0:4] = selector`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Dss.Flapper

axiom flapperBegSelectorBytes :
    selectorOf begTransition = ⟨#[0x7d, 0x78, 0x0d, 0x82]⟩

axiom flapperBidsSelectorBytes :
    selectorOf bidsTransition = ⟨#[0x44, 0x23, 0xc5, 0xf1]⟩

axiom flapperCageSelectorBytes :
    selectorOf cageTransition = ⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩

axiom flapperDealSelectorBytes :
    selectorOf dealTransition = ⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩

axiom flapperDenySelectorBytes :
    selectorOf denyTransition = ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩

axiom flapperFileSelectorBytes :
    selectorOf fileTransition = ⟨#[0x29, 0xae, 0x81, 0x14]⟩

axiom flapperFillSelectorBytes :
    selectorOf fillTransition = ⟨#[0xd9, 0xc5, 0x5c, 0xe1]⟩

axiom flapperGemSelectorBytes :
    selectorOf gemTransition = ⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩

axiom flapperKickSelectorBytes :
    selectorOf kickTransition = ⟨#[0xca, 0x40, 0xc4, 0x19]⟩

axiom flapperKicksSelectorBytes :
    selectorOf kicksTransition = ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩

axiom flapperLidSelectorBytes :
    selectorOf lidTransition = ⟨#[0x26, 0xd2, 0xad, 0xdc]⟩

axiom flapperLiveSelectorBytes :
    selectorOf liveTransition = ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩

axiom flapperRelySelectorBytes :
    selectorOf relyTransition = ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩

axiom flapperTauSelectorBytes :
    selectorOf tauTransition = ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩

axiom flapperTendSelectorBytes :
    selectorOf tendTransition = ⟨#[0x4b, 0x43, 0xed, 0x12]⟩

axiom flapperTickSelectorBytes :
    selectorOf tickTransition = ⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩

axiom flapperTtlSelectorBytes :
    selectorOf ttlTransition = ⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩

axiom flapperVatSelectorBytes :
    selectorOf vatTransition = ⟨#[0x36, 0x56, 0x9e, 0x77]⟩

axiom flapperWardsSelectorBytes :
    selectorOf wardsTransition = ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩

axiom flapperYankSelectorBytes :
    selectorOf yankTransition = ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩

end Benchmarks.Dss.Flapper
