import Examples.NestedCaller.Correct
import Lean.Util.CollectAxioms

/-! Keep the complete runtime theorem free of unfinished proofs and additional
semantic assumptions. Concrete native-decide certificates are permitted, as in
the generated RD summaries and the existing contract examples. -/
open Lean in
run_cmd do
  let allowed := #[
    ``propext, ``Classical.choice, ``Quot.sound,
    ``NestedCaller.runSelectorBytes,
    ``Ethereum.EVM.blobBN_ADD_output_chunks,
    ``Ethereum.EVM.blobBN_MUL_output_chunks,
    ``Ethereum.EVM.blobPointEval_output_chunks,
    ``Ethereum.EVM.blobRIP160_output_chunks,
    ``Ethereum.EVM.blobSNARKV_output_chunks,
    ``Ethereum.EVM.ffi_BLAKE2Compress_output_size,
    ``Ethereum.EVM.ffi_sha256_output_size]
  for ax in ← collectAxioms ``NestedCaller.nestedCallerCorrect do
    unless allowed.contains ax || (ax.toString.splitOn "._native.native_decide.ax_").length == 2 do
      throwError "Unexpected axiom in nestedCallerCorrect: {ax}"
