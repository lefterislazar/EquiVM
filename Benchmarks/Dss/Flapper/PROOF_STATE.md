# Flapper Proof State

Target: `Benchmarks.Dss.Flapper.flapperContractCorrect`

Module: `Benchmarks.Dss.Flapper`

Workdir: `Benchmarks/Dss/Flapper`

Input restrictions:
- Treat `Spec.lean`, bytecode/artifacts, generated `RuntimeBlocks_*.lean` / `CreationBlocks_*.lean`, and target theorem statements as fixed inputs.
- Edit only local proof files and notes in this directory.
- Do not inspect sibling benchmark proofs or Git history.

Exposure note:
- I accidentally ran `rg` across `Benchmarks/Dss` and saw theorem-line snippets from sibling `Correct.lean` files. I did not open those files and will not use sibling benchmark proofs as inputs.
- In this continuation I also accidentally launched one overly broad grep that produced cached/build output containing unrelated benchmark names before I stopped it. I am continuing to use only Flapper-local proof files plus shared `Reasoning` libraries as inputs.
- While locating shared `calldataWord` helpers, a grep over `Reasoning` surfaced report-file lines that mention other benchmarks. I did not open or use those benchmark proofs; the `file` proof uses local Flapper files plus shared `Reasoning` lemmas.
- While checking generic `solmExec` bridge examples, I accidentally ran a broad `grep` that printed two theorem lines from a non-Flapper benchmark. I did not open or use those proofs; the `cage` proof uses Flapper-local files plus shared `Reasoning` lemmas.
- While investigating constructor support, a grep over shared `Reasoning`/`Solm` files printed shared report lines mentioning another benchmark's constructor theorem names. I did not open or use those benchmark proofs.
- While checking storage deletion support, I accidentally launched an overly broad grep from the repository root that hit denied `.git` metadata and generated/cache metadata with unrelated benchmark names before I stopped it. I will not use that output; remaining work continues from Flapper-local files plus shared libraries only.
- While proving `yank`, a grep over shared `Reasoning` files surfaced report-file lines with unrelated benchmark names, and a later overly broad lookup-helper grep printed theorem-line snippets from non-Flapper benchmark proofs. I did not open or use those proofs; the `yank` proof uses Flapper-local files plus shared `Reasoning`/`Solm` libraries.
- While starting `kick`, I accidentally ran one grep from too high in the directory tree and it printed a few non-Flapper example/proof snippets. I did not open those files or use them; subsequent work is restricted again to Flapper-local files plus shared `Reasoning`/`Solm` libraries.
- While looking up generic storage-write lemmas for `kick`, a grep over shared `Reasoning` files also printed report-file rows that mention unrelated benchmark/example proofs. I did not open or use those proofs; the `kick` work uses Flapper-local generated summaries/proofs and shared library lemmas only.
- While resuming `deal`, I accidentally ran a broad repository-root grep for storage helpers that hit denied `.git` metadata, and an earlier broad burn-selector grep after compaction printed unrelated generated/local benchmark names. I did not open or use sibling benchmark proofs; the `deal` work continues from Flapper-local proof/generated files plus shared `Reasoning`/`Solm` libraries only.
- In the previous `deal` continuation, an accidental broad `/Benchmarks` grep printed unrelated WETH/Jug/Vat lines. I did not open or use those proofs; `deal` work remains based on Flapper-local files plus shared `Reasoning`/`Solm` libraries.
- In this continuation, two accidental root-scoped greps hit denied `.git` metadata and printed permission-denied messages. I will avoid root-scoped searches and continue with explicit Flapper/shared-library paths only.
- While finishing the constructor, an explicit shared-library grep included a non-existent top-level `Ethereum` path and printed `grep: .../Ethereum: No such file or directory`. No sibling benchmark proof content was opened or used; constructor work used Flapper-local files and shared `Reasoning`/`Solm` libraries.

Current status:
- Shared runtime guard, dispatcher, no-match, short-calldata, and body-reach facts are fully proved in `Common.lean`.
- `Correct.lean` routes the top-level runtime proof through the shared dispatcher/reach layer and per-transition body lemmas.
- Proved body lemmas with no `sorry`: `beg`, `bids`, `cage`, `deal`, `deny`, `file`, `fill`, `gem`, `kicks`, `lid`, `live`, `rely`, `tau`, `tick`, `ttl`, `vat`, `wards`, `yank`.
- Remaining unresolved body lemmas: none.
- `flapperConstructorCorrect` is proved with no `sorry`; it covers the non-payable revert path and successful constructor deployment, including generated/source storage-map equivalence for defaults, `wards`, `vat`, `gem`, and `live`.
- `Trusted.lean` contains accepted selector-byte axioms for the public selectors.
- `Kick.lean` is proved with no `sorry`: it now ties the source prefix through `fill`, `kicks`, `bids[id].bid`, `bids[id].lot`, `bids[id].guy`, and `bids[id].end` to the runtime state chain, handles the `vat.move` no-code/call-failure/call-success cases, and closes `flapperKickBody`.
- `Deal.lean` is proved with no `sorry`: it now handles decode, live/timing reverts, the `vat.move` call, the `gem.burn` call, bid deletion, checked `fill - lot`, final fill storage, and all corresponding runtime branches.
- `Tend.lean` is proved with no `sorry`: it has compiled calldata decode, selector dispatch, local-variable/source-storage eval, guard/revert branches, checked-mul/floor branches, optional refund handling, mandatory pay call handling, packed `tic` storage correspondence, and the final `flapperTendBody` bridge through both successful checked-mul/floor paths.

Next steps:
- None for this target.

Latest validation:
- `lake build Benchmarks.Dss.Flapper.Common` succeeded after adding address and uint48 helpers.
- `lake build Benchmarks.Dss.Flapper.Beg` succeeded before this continuation.
- `lake build Benchmarks.Dss.Flapper.Live Benchmarks.Dss.Flapper.Kicks Benchmarks.Dss.Flapper.Fill` succeeded.
- `lake build Benchmarks.Dss.Flapper.Lid` succeeded.
- `lake build Benchmarks.Dss.Flapper.Gem` succeeded.
- `lake build Benchmarks.Dss.Flapper.Vat` succeeded.
- `lake build Benchmarks.Dss.Flapper.Ttl Benchmarks.Dss.Flapper.Tau` succeeded.
- `lake build Benchmarks.Dss.Flapper.Wards` succeeded.
- `lake build Benchmarks.Dss.Flapper.Bids` succeeded.
- `lake build Benchmarks.Dss.Flapper.Rely` succeeded.
- `lake build Benchmarks.Dss.Flapper.Deny` succeeded.
- `lake build Benchmarks.Dss.Flapper.File` succeeded with no `sorry` warnings after proving dispatch, decode, EVM branches, Solm body branches, and final `flapperFileBody`.
- `lake build Benchmarks.Dss.Flapper.Tick` succeeded with no `sorry` warnings after proving decode, guard reverts, checked-add overflow, packed end storage, and final `flapperTickBody`.
- `lake build Benchmarks.Dss.Flapper.Cage` succeeded with no `sorry` warnings after proving decode, auth/no-code reverts, call ABI memory, typed external-call boundary, and final `flapperCageBody`.
- `lake build Benchmarks.Dss.Flapper.Yank` succeeded with no `sorry` warnings after proving decode, live/guy/no-code reverts, call ABI memory, typed external-call boundary, storage deletion correspondence, and final `flapperYankBody`. A direct grep of `Yank.lean` found no `sorry`, `admit`, or `sorryAx`.
- `lake build Benchmarks.Dss.Flapper.Kick` succeeds with no `sorry` warning after closing the full body proof.
- `lake build Benchmarks.Dss.Flapper.Deal` succeeded after closing `flapperDealBody`; a direct grep of `Deal.lean` found no `sorry`, `admit`, or `sorryAx`.
- `lake build Benchmarks.Dss.Flapper.Tend` succeeded with no `sorry` warnings after closing the two successful checked-mul/floor branches.
- `lake build Benchmarks.Dss.Flapper.Constructor` succeeded after proving constructor bytecode/source traces and the final storage-map equivalence.
- `lake build Benchmarks.Dss.Flapper.Correct` succeeded.
- `grep -RInE '\b(sorry|admit|sorryAx)\b' Benchmarks/Dss/Flapper --include='*.lean'` found no matches.
- `#print axioms Benchmarks.Dss.Flapper.flapperContractCorrect` succeeded; output contains expected classical/propext/quotient axioms, EVM FFI axioms, selector-byte axioms, and generated/native-decide facts, with no `sorryAx`.
- A follow-up filter over the axiom audit found no dependencies outside the accepted base: classical/propext/quotient axioms, EVM FFI output-size axioms, local selector-byte axioms, and generated/local/shared `native_decide.ax_*` facts.
