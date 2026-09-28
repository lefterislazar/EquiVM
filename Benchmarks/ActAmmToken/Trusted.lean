import Benchmarks.ActAmmToken.Bytecode

/-! Selector facts for the nine ABI entries in the compiled Token. -/

namespace Benchmarks.ActAmmToken

axiom allowanceSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr allowanceTransition))).extract 0 4
      = ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
axiom approveSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr approveTransition))).extract 0 4
      = ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
axiom balanceOfSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr balanceOfTransition))).extract 0 4
      = ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
axiom burnSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr burnTransition))).extract 0 4
      = ⟨#[0x42, 0x96, 0x6c, 0x68]⟩
axiom burnFromSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr burnFromTransition))).extract 0 4
      = ⟨#[0x79, 0xcc, 0x67, 0x90]⟩
axiom mintSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr mintTransition))).extract 0 4
      = ⟨#[0x40, 0xc1, 0x0f, 0x19]⟩
axiom totalSupplySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr totalSupplyTransition))).extract 0 4
      = ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
axiom transferSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr transferTransition))).extract 0 4
      = ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩
axiom transferFromSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr transferFromTransition))).extract 0 4
      = ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩

end Benchmarks.ActAmmToken
