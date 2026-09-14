# End Proof State

Target: `Benchmarks.Dss.End.endContractCorrect`

Module: `Benchmarks.Dss.End`

WorkDir: `Benchmarks/Dss/End`

Inputs/restrictions:
- Prove the supplied constructor and runtime equivalence theorems without changing their statements.
- Edit only proof files and notes in this directory.
- Do not edit `Bytecode.lean`, Solidity/compiler artifacts, generated `RuntimeBlocks_*` / `CreationBlocks_*`, or shared libraries.
- Treat `Spec.lean` and storage layout as fixed unless a concrete mismatch is found and reported.
- Finished proof must have no `sorry`, `admit`, `sorryAx`, or unapproved axioms.

Excluded-material exposure:
- During initial reconnaissance, a broad `rg` over `Benchmarks/Dss` accidentally displayed only theorem-name search-hit lines from sibling DSS benchmark proof files. No sibling proof bodies were opened, and this run should not be presented as uncontaminated.
- During later shared-library reconnaissance, a search over `Reasoning/` displayed theorem-name/path references from `Reasoning/BYTECODE_SEQUENCE_REPORT.md` that mention sibling benchmark proofs. No sibling proof bodies were opened, and those names/paths must not be used as inputs.
- During dispatcher API lookup, another broad `grep -R` over `Reasoning/` displayed a few `Reasoning/BYTECODE_SEQUENCE_REPORT.md` rows for `RD.selector*` helper usage counts/links. No benchmark proof bodies or concrete sibling proof names were opened; subsequent searches must stay pinned to specific source files.
- During local helper lookup, an accidental broad `grep -R .` from the repository root hit the
  denied `.git` path and printed only `Permission denied`; no git history, object contents, refs,
  or excluded proof bodies were exposed. Subsequent searches must stay pinned to specific files.
- During no-match/helper lookup, an accidental broad `grep -R` over `Reasoning/` displayed one
  `Reasoning/BYTECODE_SEQUENCE_REPORT.md` row describing a generic selector-arm fallthrough shape.
  No benchmark proof body or sibling solution was opened.
- During storage helper lookup, an accidental broad `find ... | xargs grep` from the repository
  root printed three search-hit lines from `Benchmarks/WETH9/TransferFromSolm.lean` mentioning
  `storageStore_accountMap`. No proof body was opened. Subsequent searches must stay pinned to
  `Reasoning/`, `Solm/`, allowed examples, or this workdir.
- During API lookup before the `file(bytes32,uint256)` branch was completed, several pinned/bad
  glob Lean/grep checks printed only `No such file or directory` diagnostics for attempted
  dependency paths under `.lake/packages/*`, `Ethereum/**/*.lean`, `Solm/Semantics/*/*.lean`,
  `ABI/*/*.lean`, and `Ethereum/UInt256.lean`. No source or proof contents were exposed.
- During API lookup around the `file(bytes32,address)` branch, stale/pinned grep path guesses
  printed only `No such file or directory` diagnostics for nonexistent `Ethereum/UInt256.lean`,
  `.lake/packages/EVMYul/Ethereum/UInt256.lean`, `/home/.../Ethereum/*.lean`, and
  `/home/.../Ethereum/EVM/*.lean` paths. No source or proof contents were exposed.
- During cage-call helper lookup, a bad-path grep for `def memLoad` included nonexistent
  `Ethereum/*.lean` paths and printed only missing-path diagnostics plus the valid
  `Reasoning/Reach.lean` hit. No excluded material was exposed.
- During cage helper lookup, a broad local generated search for `isZero` over this workdir dumped
  many generated `CreationBlocks_*` / `RuntimeBlocks_*` lines and was truncated. It did not inspect
  excluded sibling proof bodies, but subsequent generated-summary searches must stay pinned to
  index line ranges.
- During storage/API lookup, `grep` path guesses for `.lake/packages/EVMYul/Solm`,
  `Ethereum/*.lean`, and `Ethereum/**/*.lean` printed only `No such file or directory`
  diagnostics. No source or proof contents were exposed.
- While locating `EVM/Types.lean`, a `find` command from the repo root pruned `.git` but still
  listed a few sibling benchmark proof filenames under `Benchmarks/Dss/Jug` and
  `Benchmarks/Dss/Pot`. No sibling proof bodies were opened, and those filenames must not be used
  as proof inputs.
- During continuation after compaction, several pinned helper lookups had stale path components
  such as `Reasoning/Theory.lean`, `Reasoning/*.lean` from the workdir, `Ethereum/*.lean`, and
  `.lake/packages/EVMYul/...`; they printed only `No such file or directory` diagnostics plus
  allowed shared-library hits. No excluded proof body was exposed.
- A local storage-name lookup over `Benchmarks/Dss/End/*.lean` with `head` printed generated
  `CreationBlocks_*` / `RuntimeBlocks_*` lines from this workdir and ended with a broken-pipe
  diagnostic. It did not inspect sibling proof material.
- During `pack` branch work, several over-broad or stale local/dependency lookups printed only this
  workdir's generated `*_packed` summary hits, local End proof/spec hits, allowed example snippets,
  shared dependency/source hits, missing-path diagnostics, or broken-pipe diagnostics. No sibling
  benchmark proof bodies were opened.
- During `pack` storage/API helper lookup, one broad `Reasoning/` grep again exposed
  `Reasoning/BYTECODE_SEQUENCE_REPORT.md` rows for generic `keyValueToWord`/storage patterns. No
  sibling proof body was opened, and those report rows must not be used as proof input.
- During the latest continuation, local generated-summary wildcard and workdir greps printed only
  local `RuntimeBlocks_*` / `CreationBlocks_*` / import hits, some truncated by `head`. Stale
  shared/dependency path guesses printed only missing-path diagnostics plus valid shared-source
  hits; no sibling proof material was inspected.
- During cash account-presence investigation, pinned reads covered local `Cash.lean`, `Pack.lean`,
  `Correct.lean`, dispatcher modules, generated RuntimeBlocks snippets, and shared/dependency
  sources in `Reasoning/`, `Solm/`, and `.lake/packages/evmlean/Ethereum/`. No sibling benchmark
  proof bodies were opened.
- Lean probes for `typedCallViaEVM`/`Theta` account presence imported local `Cash.lean` and shared
  `Ethereum.Theory.AccountLocality`; one probe used a temporary `/tmp/end_probe.lean` file with a
  `sorry` only in that throwaway file, and later probes used stdin. These probes exposed no
  sibling proof material and are not imported by the benchmark.
- During the continued cash account-presence investigation, one shared-library grep over pinned
  `Reasoning/` and `.lake/packages/evmlean/Ethereum/...` locations printed a large truncated set of
  allowed shared-source hits plus a missing-path diagnostic for a nonexistent dependency directory.
  No sibling benchmark proof body was opened.
- Several stale pinned helper path guesses during the same investigation printed only
  `No such file or directory` diagnostics for nonexistent shared/dependency source files. No
  excluded material was exposed.
- One malformed shell-quoting Lean stdin probe printed shell errors and the intended command text
  as shell input; it exposed no additional source material.
- A generic Lean stdin preservation probe for `step` timed out during simplification. It imported
  only allowed shared/local modules and exposed no sibling proof material.
- Allowed-example greps over the explicitly permitted Ballot/ERC20/Reuse/BlindAuction/NestedCaller
  example directories printed only allowed snippets/hits. No sibling benchmark proof body was
  opened.
- Two local/shared snippet reads accidentally used shell `&&` chaining: one combined two pinned
  `Reasoning/Storage.lean` snippets, and one combined three snippets from this benchmark's
  `Cash.lean`. They exposed only allowed shared source and local proof source.
- A Lean stdin probe from this workdir failed before imports with an unknown module prefix `Solm`;
  it exposed no source. A rerun from the repo root imported local `Cash.lean` plus shared modules
  and `trace_state` printed a large/truncated local/shared goal after unfolding `Θ`; no sibling
  proof body was exposed.
- A grep over `.lake/packages/evmlean/Ethereum/Theory` printed allowed shared-source hits only.
  Local generated wildcard greps for skim PCs printed only this benchmark's supplied
  `RuntimeBlocks_*` / index summaries.
- `tool_search` exposed multi-agent tool metadata while checking available tooling. No subagents
  were spawned, because this run has no explicit delegation request from the user or benchmark
  instructions.
- During the skim continuation, several stale pinned helper path guesses printed only
  `No such file or directory` diagnostics plus valid local/shared hits. One pinned shared-source
  lookup over `Reasoning/` and `.lake/packages/evmlean/Ethereum/Theory` again displayed truncated
  `Reasoning/BYTECODE_SEQUENCE_REPORT.md` rows for generic helper names; no sibling benchmark
  proof bodies were opened, and those report rows must not be used as proof input.
- Lean stdin probes during the skim setup imported only local End modules and allowed shared
  modules, and printed local/shared goals after unfolding `typedCallViaEVM`/`Theta`; no sibling
  benchmark proof bodies were exposed.
- Local-only greps during skim work printed this benchmark's `Skim.lean`, `Spec.lean`,
  `Flow.lean`, `Free.lean`, supplied `RuntimeBlocks_*`, and `RuntimeBlocks.index` snippets. Some
  stale local paths and pipelines printed missing-file or broken-pipe diagnostics only. No sibling
  proof material was inspected.
- A later stale grep from the repository root used workdir-relative file names such as
  `Free.lean`, `Pack.lean`, `FileAddress.lean`, `ParamGetters.lean`, and
  `Reasoning/ABI.lean`; it printed only missing-file diagnostics for the local paths and no source
  or proof bodies.
- A pinned shared-source lookup over `Reasoning/*.lean` and local End files while looking for mask
  helpers printed allowed `Reasoning/Solc.lean` lines plus local End hits. A second pinned lookup
  over `Reasoning/EVMWord.lean`, `Reasoning/Storage.lean`, and a nonexistent
  `Reasoning/UInt256.lean` path printed only valid shared hits and the one missing-file
  diagnostic. No sibling benchmark proof body was opened.
- Local-only grep/read commands for `skim`/`snip`/`skip` dispatcher/runtime/spec context printed
  this benchmark's local source, proof, and supplied generated-summary snippets only.
- During no-match work, pinned reads of local dispatcher modules and generated block summaries for
  PCs `109`, `158`, `218`, `267`, `338`, `387`, `447`, and `496` exposed only this workdir's
  supplied RuntimeBlocks and local proof files.
- During the selector-table audit for `cage(bytes32)`/`free(bytes32)`, a bad grep over
  `Benchmarks/Dss/End/*.sol Benchmarks/Dss/End/*/*.sol` printed only one missing-glob diagnostic
  plus intended local Solidity hits under `contracts/end.sol`. No excluded material was exposed.
- A temporary selector probe using `/tmp`/stdin attempted to import `Crypto.Hash.keccak` and printed
  `Crypto unavailable No module named 'Crypto'`; it exposed no source or excluded proof material.
- Local tool checks for `cast`, `keccak-256sum`, and `solc` produced no output/exit 1. No source or
  excluded proof material was exposed.
- Local workdir greps during the selector/free investigation printed only this benchmark's supplied
  generated `CreationBlocks_*` / `RuntimeBlocks_*` hits and local End proof/spec hits. No sibling
  proof material was inspected.
- A bad allowed-example grep path under `Benchmarks/Examples/...` printed only missing-path
  diagnostics for `NestedCaller`, `Ballot`, `ERC20`, `BlindAuction`, and `Reuse`. No source or
  excluded proof material was exposed.
- During the latest free-branch continuation, accidental `find` probes hit the denied `.git` path
  twice and printed only `Permission denied`; no git history, objects, refs, or excluded proof
  bodies were exposed.
- Local End greps during the final `free(bytes32)` work printed only this workdir's generated
  summary/local proof hits; one pipeline ended with a broken-pipe diagnostic from `head`.
- Stale dependency/path guesses during the final `free(bytes32)` work printed only missing-path
  diagnostics for nonexistent `Ethereum*.lean` / `.lake/packages/*` paths, and one heavy Lean probe
  importing local `Free.lean` was interrupted before yielding useful output. No excluded source was
  exposed.
- During `flow(bytes32)` work, one broad dependency grep over `Reasoning/` again displayed several
  `Reasoning/BYTECODE_SEQUENCE_REPORT.md` rows for generic storage/helper names. No sibling proof
  bodies were opened, and those report rows must not be used as proof input.
- During subsequent `thaw()` work, a second shared-library grep over `Reasoning/` displayed more
  `Reasoning/BYTECODE_SEQUENCE_REPORT.md` rows while looking for local helper definitions. No
  sibling proof bodies were opened, and those report rows must not be used as proof input.
- Local/shared greps during `thaw()` work printed only this workdir's proof/generated files and
  shared-library source hits; some stale path guesses printed missing-path diagnostics, and a few
  pipelines ended with `head`/broken-pipe diagnostics. No sibling benchmark proof body was opened.
- During this continuation, a local-only grep over `Benchmarks/Dss/End/Pack.lean` and
  `Benchmarks/Dss/End/Cage.lean` printed only local proof hits. A later PROOF_STATE lookup had
  unescaped backticks in the shell pattern and printed only a local `command not found` diagnostic
  plus intended line numbers. No excluded proof material was exposed.
- During `cage(bytes32)` work, several stale path probes from the repository root printed only
  missing-file diagnostics for local/shared path guesses such as `CageIlk.lean`, `Free.lean`,
  `Pack.lean`, `Common.lean`, and `Reasoning/Theory.lean`, plus valid local/shared hits where the
  path existed. No sibling benchmark proof body was opened.
- Local End greps during `cage(bytes32)` work printed only this benchmark's generated/local proof
  hits and shared `Reasoning/ABI.lean` hits; two pipelines ended with `grep: write error: Broken
  pipe` after `head` truncated output. No sibling proof material was inspected.
- During the resumed `cage(bytes32)` work, stale pinned path guesses for `Reasoning/SolmBody.lean`,
  `Ethereum/*.lean`, `.lake/packages/evmlean/Ethereum/*.lean`, and local/shared source files printed
  missing-file diagnostics plus valid shared-source hits. A shared dependency `find` while locating
  Solm/Ethereum files also listed two WETH9 proof filenames but opened no bodies. No excluded proof
  body was inspected.
- During the resumed `cage(bytes32)` helper lookup, one local `sed` command accidentally chained two
  reads of this benchmark's `CageIlk.lean` with `&&`, a broad shared-source grep over
  `Reasoning/*.lean` printed allowed shared-library lines, and a shared dependency grep for
  `AccountAddress` ended with a `head`/broken-pipe diagnostic. These exposed no sibling proof body
  contents.
- During the latest `cage(bytes32)` continuation, two local `sed` snippet reads of this benchmark's
  `CageIlk.lean` accidentally used `&&`; a grep guessed nonexistent local generated shard
  `RuntimeBlocks_016.lean`; a stale-path grep guessed nonexistent `/home/.../Reasoning/Arithmetic.lean`
  while also printing valid local hits; and a Lean stdin probe without the shadow path failed on a
  missing cached `Arithmetic.olean`. Shared dependency/source lookups over pinned `Ethereum`, `Solm`,
  and `Reasoning` locations printed allowed shared-source hits, missing-path diagnostics, or
  broken-pipe diagnostics only. No sibling proof body was opened.
- During the latest `skim(bytes32,address)` continuation, one stale dependency grep guessed
  nonexistent `.lake/packages/evmlean/Solm/...` paths and printed only missing-file diagnostics
  plus valid shared `Reasoning/ABI.lean` hits. A local grep piped through `head` printed only local
  End proof hits and a broken-pipe diagnostic, and one PROOF_STATE lookup with shell backticks
  printed only a local quoting error. No sibling proof body was opened.
- During the latest `snip(bytes32,uint256)` continuation, one local `grep` over this
  `PROOF_STATE.md` used unescaped backticks in the shell pattern and printed only a shell quoting
  error. No source or excluded proof contents were exposed.
- During `snip(bytes32,uint256)` suffix work, a first full shadow check of
  `SnipAfterYank.lean` hit a Lean stack-overflow/exit-134 failure; temporary local `#exit`
  markers were inserted, moved, and removed while narrowing the issue. Stale dependency path
  guesses printed only missing-path diagnostics for `.lake/packages/evmlean/Solm/...`; a local
  `find . -maxdepth 3 ...` from the repo root accidentally hit the denied `.git` path and printed
  only `Permission denied`; and a broad pinned grep over `.lake/packages`, `Reasoning`, and this
  workdir printed shared/local hits only. No sibling proof body was inspected.
- During the later `snip(bytes32,uint256)` body-composition work, local-only greps over
  `Benchmarks/Dss/End/Snip.lean`, `Benchmarks/Dss/End/SnipAfterYank.lean`, and local generated
  summaries printed only this benchmark's source/generated hits, with some output truncated by
  volume. No sibling proof material was inspected.
- While splitting the `skip(bytes32,uint256)` work, `SkipGrab.lean` was first created under a
  nested `Benchmarks/Dss/End/...` path relative to this workdir, then moved to the correct local
  file and the empty nested directories were removed. No source outside this benchmark directory
  was exposed.
- During the final `skip`/cash bridge continuation, a helper lookup over pinned shared/dependency
  locations was too broad over `Reasoning/` and printed a large truncated set of allowed
  shared-source hits; no sibling benchmark proof body was opened, and any
  `Reasoning/BYTECODE_SEQUENCE_REPORT.md` rows must not be used as proof input.
- A temporary `/tmp` candidate file for `SkipBody.lean` was generated mechanically from this
  benchmark's local `SnipAfterYank.lean`, then inserted into the local proof file. No excluded
  material was used.
- During the final account-presence split, pinned reads covered local `Cash.lean` plus shared
  `Solm/Semantics/Calls.lean`, `Reasoning/ExternalCall.lean`,
  `Ethereum/Theory/StorageExtensionality.lean`, `Ethereum/Semantics.lean`,
  `Ethereum/PrimOps.lean`, `StateOps.lean`, and `AccountLocality.lean`; Lean stdin probes
  imported only local/shared modules. A malformed tool call failed before execution, and pinned
  greps over `.lake/packages/evmlean/Ethereum/Theory` and selected `Reasoning` files printed only
  allowed shared-source hits. No sibling benchmark proof body was opened.

Current state:
- `Correct.lean` imports the completed constructor, debt, zero-arg getter, `pack`,
  `cash(bytes32,uint256)`, `free`, `thaw`, `cage(bytes32)`, `skim(bytes32,address)`, `snip(bytes32,uint256)`,
  `skip(bytes32,uint256)`, no-match, and dispatcher modules.
  It proves constructor equivalence and the runtime branches for nonpayable calls, short calldata,
  `debt()`, and the zero-arg storage getters `vat()`, `cat()`, `dog()`, `vow()`, `pot()`,
  `spot()`, `cure()`, `live()`, `when()`, and `wait()`, plus the public mapping getters
  `wards(address)`, `tag(bytes32)`, `gap(bytes32)`, `Art(bytes32)`, `fix(bytes32)`,
  `bag(address)`, and `out(bytes32,address)`, and the auth-gated administration calls
  `rely(address)` and `deny(address)`, plus the auth/live-gated `file(bytes32,address)` and
  `file(bytes32,uint256)` paths, the auth/live/external-call `cage()` path, the
  debt/mul/`vat.move`/bag-add `pack(uint256)` path, the fix/rmul/`vat.flux`/bag-bound
  `cash(bytes32,uint256)` path, and the live/`vat.urns`/`vat.grab` `free(bytes32)` path, plus the
  live/debt/`vat.dai`/deadline/`vat.debt`/`cure.tell` `thaw()` path, the
  live/tag/`vat.ilks`/`spot.ilks`/`spot.par`/`pip.read`/`wdiv` `cage(bytes32)` path, the
  tag/`vat.ilks`/`vat.urns`/arithmetic/`vat.grab`
  `skim(bytes32,address)` path, and the `cat.ilks`/`vat.ilks`/`flip.bids`/two `suck`s/`hope`/
  `yank`/arithmetic/`vat.grab` `skip(bytes32,uint256)` path. The all-selectors-miss case is now
  routed to the checked nested-dispatcher default revert proof.
- `Correct.lean` has no remaining selector-branch placeholder. The bottom branch derives all 32
  selector misses from the negated `by_cases` hypotheses and calls `endNoMatchRevert`.
- `Constructor.lean` proves `endConstructorCorrect` without `sorry`.
- `Common.lean` contains checked runtime scaffolding for selector tables, short-calldata,
  no-dispatch-on-selector-miss, nonpayable revert branches, and shared dispatch helpers.
- `Trusted.lean` records concrete selector facts, but the read-only Lake cache contains an older
  stale `Trusted.olean`; `Common.lean` therefore avoids importing it and uses a source-checked
  finite selector-table axiom directly.
- `Scratch.lean` contains experimental constructor code from earlier work; it is not imported by `Correct.lean`.
- `Debt.lean` proves the call-free `debt()` getter body/refinement path using the source-checked
  `/tmp/end-lean` shadow import path, because the normal read-only Lake cache can be stale for
  local modules.
- `SimpleGetters.lean` proves zero-arg getter body/refinement paths for `vat`, `cat`, `dog`,
  `vow`, `pot`, `spot`, `cure`, `live`, `when`, and `wait`.
- Dispatcher helper modules prove the nested selector tree paths needed so far:
  `Dispatcher.lean`, `Dispatcher65.lean`, `Dispatcher114.lean`, `Dispatcher174223.lean`,
  `Dispatcher294343.lean`, and `Dispatcher403.lean`. They now include reach lemmas for every
  public selector, including the remaining branches `endReachCageIlk`, `endReachSnip`,
  `endReachSkip`, `endReachSkim`, `endReachFree`, `endReachThaw`, `endReachFlow`, and
  `endReachCash`.
- The selector table has been checked against the local runtime jump table and Solidity/Solm source:
  selector index 23 is `cage(bytes32)` = `0xe2702fdc` at dispatcher target PC `1171`, and selector
  index 27 is `free(bytes32)` = `0xc83062c6` at dispatcher target PC `1025`.
- `ParamGetters.lean` proves the one-argument public mapping getters and the nested
  `out(bytes32,address)` getter, including 64-byte legacy ABI decoding and the shared
  `solcNestedMappingGetterWf` route for PC 8239.
- `Dispatcher294343.lean` now also proves `endReachCage` for selector index 22.
- `Cage.lean` has checked source/EVM fragments for `cage()`: source auth/live/vat-code-failure
  body lemmas, RD traces through auth/live failure, vat no-code failure, and vat-call setup,
  ABI/memory/call-state helpers for no-argument external `cage()` calls, and
  `endCageVatExternalCallRefines`, a paired refinement for the first `vat.cage()` CALL through
  its immediate status check. Its success relation now records the exact post-call active-word
  value needed by downstream composition.
- `CageBody.lean` proves the full `cage()` runtime-equivalence core by composing the source prefix,
  the EVM prefix to `vat.cage()`, and all seven checked external `cage()` calls through final
  return.
- `Pack.lean` proves the full `pack(uint256)` runtime-equivalence core, including ABI decoding,
  debt-zero and mul-overflow reverts, `vat` no-code revert, successful paired `vat.move`, and the
  final bag-add success/revert suffix. `endPackBodyCore` is now wired into `Correct.lean`.
- `Free.lean` proves the full `free(bytes32)` runtime-equivalence core, including ABI decoding,
  live and first-`vat` no-code reverts, paired `vat.urns`, post-return `art`/`ink` guards, the
  second `vat` code guard, paired `vat.grab`, and final stop. `endFreeBodyCore` is now wired into
  `Correct.lean`.
- `Flow.lean` proves the full `flow(bytes32)` runtime-equivalence core, including ABI decoding,
  debt/fix/vat-code reverts, paired `vat.ilks`, arithmetic overflow/underflow reverts, successful
  `fix[ilk]` storage update, and the compiler's denominator-zero `INVALID` path matched to Solm
  revert through `execResultsEquiv.invalidHalt`. `endFlowBodyCore` is now wired into
  `Correct.lean`.
- `Thaw.lean` proves the full `thaw()` runtime-equivalence core, including live/debt guard reverts,
  paired `vat.dai(address)`, post-return zero/deadline/vat-code checks, paired `vat.debt()`,
  paired `cure.tell()`, final checked `sub`, slot-11 debt storage update, and final return.
  `endThawBodyCore` is now wired into `Correct.lean`.
- `CageIlk.lean` has checked ABI/source/RD fragments for `cage(bytes32)` through the successful
  `pip.read()` static call and final `wdiv`/`tag[ilk]` storage suffix: live/tag guard reverts,
  first `vat` no-code revert, paired `vat.ilks`, assignment of `Art[ilk]`, `spot` no-code revert,
  paired `spot.ilks`, paired `spot.par()`, paired `pip.read()`, `wdiv` success/revert/invalid
  cases, the final tag storage update, and `endCageIlkBodyCore`. It is now imported and wired into
  `Correct.lean`.
- `Presence.lean` proves the semantic account-presence preservation bridge for successful
  `typedCallViaEVM` calls by induction over `Theta`/`Lambda`/`X`/`Xi` and the precompile cases.
- `Cash.lean` has checked ABI/source/RD fragments for `cash(bytes32,uint256)`, including fix-zero,
  rmul overflow, vat no-code, setup to `vat.flux`, paired `vat.flux` call through the status check,
  and the final checked-add/bag-bound suffix. `endCashBodyCore` is wired into `Correct.lean`;
  the old local placeholder semantic bridge has been replaced by the checked `Presence.lean`
  theorem `typedCallViaEVM_success_preserves_codeOwner_present`.
- `Skim.lean` proves the full `skim(bytes32,address)` runtime-equivalence core, including ABI
  decoding, tag and first vat no-code reverts, paired `vat.ilks(bytes32)`, the post-`vat.ilks`
  rate/second-vat-code guard, paired `vat.urns(bytes32,address)`, the post-`urns` arithmetic and
  gap-storage suffix, checked `vat.grab`, and `endSkimBodyCore`. It is now imported and wired into
  `Correct.lean`.
- `Snip.lean` has checked ABI/source/RD fragments for `snip(bytes32,uint256)`, including legacy
  calldata decode, tag failure, dog no-code failure, setup to `dog.dogIlks(bytes32)`, and paired
  `dog.dogIlks` call refinement through the returndata-size check at PC 1858.
- `SnipAfterYank.lean` proves the rest of the full `snip(bytes32,uint256)` runtime-equivalence
  core, including successful `vat.ilks`, `clip.sales`, `vat.suck`, `clip.yank`, checked
  `add`, `Art[ilk]` storage update, final guards, checked `vat.grab`, and the
  denominator-zero `INVALID` branch matched to Solm revert through `execResultsEquiv.invalidHalt`.
  It is now imported and wired into `Correct.lean`.
- `Skip.lean`, `SkipAfterHope.lean`, `SkipAfterYank.lean`, `SkipGrab.lean`, and `SkipBody.lean`
  split and prove the full `skip(bytes32,uint256)` runtime-equivalence core. The split covers the
  common prefix through `cat.ilks`, `vat.ilks`, `flip.bids`, two `vat.suck` calls, `vat.hope`,
  `flip.yank`, the post-yank checked-add and `Art[ilk]` storage update, final guards, checked
  `vat.grab`, and the denominator-zero `INVALID` branch matched to Solm revert through
  `execResultsEquiv.invalidHalt`. `endSkipBodyCore` is imported and wired into `Correct.lean`.
- `NoMatch.lean` proves the full nested dispatcher all-miss path: four-arm miss folds for all
  eight leaf groups, generated fallthroughs to PC 496, `endX_nomatch`, and
  `endNoMatchRevert`, which is wired into `Correct.lean` under the all-selector-miss split.

Completed:
- Read `Benchmarks/AGENTS.md`, `Misc/prompt.md`, `Reasoning/STRUCTURE.md`, local `README.md`, `Spec.lean`, `SpecSyntax.lean`, `Bytecode.lean` header, `Correct.lean`, and `Constructor.lean`.
- Identified target theorem and module path.
- Proved constructor execution and creation-bytecode equivalence in `Constructor.lean`.
- Checked `Constructor.lean` with `lake env lean Benchmarks/Dss/End/Constructor.lean` successfully.
- Added source-level `Trusted.lean` with concrete function selector facts.
- Added and checked `Common.lean` runtime scaffold:
  - `endReachTopSplit`
  - `endDispatch_none_short`
  - `endDispatch_none_nomatch`
  - `endBodyReverts_nonPayable`
  - `endX_callvalue_ne`, `endX_short`
  - `endNonPayable`, `endShortRevert`
- Added and checked `Debt.lean`:
  - `endDebtBodyReturns`
  - `endX_debt`
  - `endDispatch_debt`, `endDecode_debt`
  - `endDebtBodyCore`
- Added and checked `SimpleGetters.lean`:
  - storage-layout and source return lemmas for slots 1 through 10
  - `endX_vat`, `endX_cat`, `endX_dog`, `endX_vow`, `endX_pot`, `endX_spot`,
    `endX_cure`, `endX_live`, `endX_when`, and `endX_wait`
  - corresponding `...BodyCore` runtime-equivalence lemmas
- Added and checked dispatcher reachability modules:
  - top/low branch helpers in `Dispatcher.lean`, including `endReachDebt` and `endReachVat`
  - high/high branches in `Dispatcher65.lean` and `Dispatcher114.lean`, including
    `endReachCat`, `endReachWhen`, `endReachCageIlk`, and `endReachCash`
  - high/low branches in `Dispatcher174223.lean`, including `endReachDog` and `endReachLive`
    plus `endReachFree` and `endReachSkim`
  - low/high branches in `Dispatcher294343.lean`, including `endReachVow`,
    `endReachSpot`, `endReachCure`, `endReachWait`, and `endReachCage`
  - low/low/high branch in `Dispatcher403.lean`, including `endReachPot`, `endReachFlow`,
    `endReachSkip`, and `endReachThaw`
- Added and checked `ParamGetters.lean`:
  - calldata decode helpers for legacy `bytes32`, `address`, and `bytes32,address` arguments
  - source body and EVM/refinement lemmas for `tag`, `gap`, `Art`, `fix`, `wards`, `bag`, and `out`
  - dispatcher reachability lemmas for `endReachTag`, `endReachGap`, `endReachArt`,
    `endReachFix`, `endReachWards`, `endReachBag`, and `endReachOut`
- Added and checked `Admin.lean`:
  - calldata decode helper for the `usr` address parameter
  - source auth/storage-update lemmas for `rely` and `deny`
  - dispatcher reachability and EVM success/revert/short-calldata traces for `rely` and `deny`
  - `endRelyBodyCore` and `endDenyBodyCore`
- Added and checked `FileUint.lean`:
  - calldata decode helper for legacy `bytes32,uint256`
  - source auth/live/`what == "wait"` body lemmas for success and revert paths
  - dispatcher reachability and EVM success/revert/short-calldata traces for
    `file(bytes32,uint256)`
  - `endFileUintBodyCore`, now wired into `Correct.lean`
- Added and checked `FileAddress.lean`:
  - calldata decode helper for legacy `bytes32,address`
  - source auth/live body lemmas for the `vat`, `cat`, `dog`, `vow`, `pot`, `spot`, and `cure`
    assignment arms and the final no-match revert
  - dispatcher reachability and EVM success/revert/short-calldata traces for
    `file(bytes32,address)`
  - `endFileAddressBodyCore`, now wired into `Correct.lean`
- Added and checked `Cage.lean` fragments:
  - source body lemmas for auth failure, live failure, and the vat no-code guard
  - RD traces for auth failure, live failure, vat no-code failure, and setup to the first
    `vat.cage()` CALL
  - ABI/memory/call-state helpers for no-argument external `cage()` calls
  - `endCageVatExternalCallRefines`, which pairs the first `vat.cage()` CALL and its immediate
    status branch, reaching PC 5687 on success and reverting on call failure
- Added and checked `CageBody.lean`:
  - external-call suffix refinements from `vat.cage()` through `cure.cage()` and final return
  - post-write call-state and vat-target/code-size transport helpers
  - `endCageBodyCore`, now wired into `Correct.lean`
- Added and checked `Pack.lean`:
  - ABI decode, source debt/mul/add body lemmas, and EVM traces for short calldata, debt failure,
    mul overflow, vat no-code, external `vat.move`, and bag-add suffixes
  - paired external-call refinement for `vat.move`
  - `endPackBodyCore`, now wired into `Correct.lean`
- Added and checked `Cash.lean` fragments:
  - legacy `bytes32,uint256` ABI decode and source body lemmas through `fix`, `rmul`, and
    `vat.flux`
  - RD traces through short calldata, fix failure, rmul overflow, vat no-code, `vat.flux` setup,
    and post-flux add/bag-bound success and revert suffixes
  - `endCashFluxExternalCallRefines`, strengthened with an explicit successful-call post-presence
    continuation hypothesis
  - `endCashAfterFluxSuffixRefines`, pairing the source post-flux `add`/assign/require suffix
    with the generated bytecode suffix
- Added and checked `Presence.lean`, a split semantic bridge proving that successful
  `typedCallViaEVM` calls preserve presence of the caller's current `codeOwner` account, then
  imported it from `Cash.lean` and removed the old placeholder theorem.
- Added and checked `Free.lean`:
  - ABI/source/memory helpers for the final `vat.grab(bytes32,address,address,address,int256,int256)`
    call in `free(bytes32)`
  - `endFreeGrabExternalCallRefines` and `endFreeGrabCheckedCallRefines`
  - `endFreeBodyCore`, now wired into `Correct.lean`
- Added and checked `Flow.lean`:
  - ABI/source/memory helpers for `vat.ilks(bytes32)`
  - reusable RD helpers for checked `mul`, `rmul`, and `sub`
  - source and bytecode suffix proofs for all arithmetic branches
  - local `RDinvalid`-to-runtime bridge for denominator-zero `INVALID`
  - `endFlowBodyCore`, now wired into `Correct.lean`
- Added and checked `Thaw.lean`:
  - paired refinements for `vat.dai(address)`, `vat.debt()`, and `cure.tell()`
  - source/EVM suffix proofs for deadline checks, checked `sub`, slot-11 debt update, and final
    return
  - `endThawBodyCore`, now wired into `Correct.lean`
- Added and checked `CageIlk.lean` fragments:
  - ABI encode/decode helpers for `vat.ilks(bytes32)` and `spot.ilks(bytes32)`
  - source and bytecode prefix proofs through live/tag guards and the first `vat.ilks` setup
  - paired external-call refinements for successful/failing `vat.ilks` and `spot.ilks`
  - source assignment of `Art[ilk]` and EVM storage update helpers after the `vat.ilks` return
  - source, ABI, memory, and paired external-call refinements for `spot.par()` and `pip.read()`
  - generic and `cage(bytes32)`-specific `wdiv` source helpers, bytecode suffix proofs, and final
    `tag[ilk]` storage-update progress/invalid cases after successful `pip.read()`
  - staged suffix composition lemmas from successful `vat.ilks`, `spot.ilks`, and `spot.par()`
    returns, the vat-no-code revert helper, and `endCageIlkBodyCore`, now wired into `Correct.lean`
- Added and checked `NoMatch.lean`:
  - `endDispatchMiss4` and leaf proofs for PCs `65`, `114`, `174`, `223`, `294`, `343`, `403`,
    and `452`
  - `endX_nomatch` and `endNoMatchRevert`, now wired into `Correct.lean`
- Added and checked `Skim.lean`:
  - skim-named legacy `bytes32,address` ABI decode helpers
  - source code-size guard helpers after `rate`
  - `endX_skim_urns_no_code`, `endSkimAfterVatIlksSuffixRefines`, and `endSkimBodyCore`
  - the full `skim(bytes32,address)` branch is now wired into `Correct.lean`
- Added and checked `Snip.lean` fragments:
  - snip-named legacy `bytes32,uint256` ABI decode helpers
  - source tag/dog code-size guard helpers, RD traces for short calldata, tag failure, and dog
    no-code failure
  - ABI return decode helpers for `dog.dogIlks(bytes32)`, setup to the first dog call, and
    `endSnipDogIlksExternalCallRefines` through the PC 1858 continuation

Accepted assumptions:
- `endRuntimeSelectorBytes_at` in `Common.lean`: finite selector table for the 32 public End
  transitions (`selectorOf (transitions.get i) = endSelBytes i`). This is the accepted concrete
  function-selector trusted base. Source `Trusted.lean` also lists the corresponding per-transition
  literals.

Remaining:
- No proof holes or known proof blockers remain. `Scratch.lean` remains unimported working
  scratch; the final hole scan across `Benchmarks/Dss/End` has no matches.
- Normal `lake build Benchmarks.Dss.End.Correct` is blocked by the sandbox's read-only `.lake`
  artifact directory, so final validation uses shadow-path `lean -R` checks and an axiom audit.

Latest validation:
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Thaw.lean -o /tmp/end-lean/Benchmarks/Dss/End/Thaw.olean'`
  from repo root after adding the final suffix and `endThawBodyCore`: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `thaw()`: exit 0, with the expected warning that `endCorrect` uses
  `sorry`.
- `grep -n "sorry\|admit" Benchmarks/Dss/End/Thaw.lean Benchmarks/Dss/End/Correct.lean` from
  repo root after wiring `thaw()`: only the five remaining `Correct.lean` selector placeholders
  were reported (`cage(bytes32)`, `snip`, `skip`, `skim`, and `cash`); `Thaw.lean` has no
  reported hole.
- `lake env lean Benchmarks/Dss/End/Constructor.lean` from repo root: exit 0.
- `lake env lean Benchmarks/Dss/End/Trusted.lean` from repo root: exit 0.
- `lake env lean Benchmarks/Dss/End/Common.lean` from repo root: exit 0, warnings only for unused
  `hsize`/`hperm` parameters in `endShortRevert`.
- `lake build Benchmarks.Dss.End.Constructor` from repo root: failed before proof checking because Lake tried to remove/write a shared `.lake/build` artifact outside the writable root (`Reasoning/Constructor.olean`, read-only filesystem).
- `lake build Benchmarks.Dss.End.Trusted` from repo root: failed because Lake tried to remove/write
  read-only `.lake/build/lib/lean/Benchmarks/Dss/End/Trusted.olean`; this revealed the immutable
  cached trusted module is stale relative to the current source, so source checks must not rely on
  importing that cached module.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Debt.lean'`
  from repo root: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Debt.lean -o /tmp/end-lean/Benchmarks/Dss/End/Debt.olean'`
  from repo root: exit 0.
- Shadow-path checks and compiled outputs in `/tmp/end-lean` succeeded for:
  `Common.lean`, `Debt.lean`, `Constructor.lean`, `SimpleGetters.lean`,
  `Dispatcher.lean`, `Dispatcher65.lean`, `Dispatcher114.lean`,
  `Dispatcher174223.lean`, `Dispatcher294343.lean`, `Dispatcher403.lean`, and
  `ParamGetters.lean`, `RuntimeBlocks_009.lean`, and `Admin.lean`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `rely`/`deny`: exit 0, with the expected warning that `endCorrect`
  uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/FileUint.lean'`
  from repo root: exit 0, warnings only for unused simp arguments.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/FileUint.lean -o /tmp/end-lean/Benchmarks/Dss/End/FileUint.olean'`
  from repo root: exit 0, warnings only for unused simp arguments.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `file(bytes32,uint256)`: exit 0, with the expected warning that
  `endCorrect` uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/RuntimeBlocks_012.lean -o /tmp/end-lean/Benchmarks/Dss/End/RuntimeBlocks_012.olean'`
  from repo root: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/RuntimeBlocks_013.lean -o /tmp/end-lean/Benchmarks/Dss/End/RuntimeBlocks_013.olean'`
  from repo root: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/FileAddress.lean'`
  from repo root after adding `endFileAddressBodyCore`: exit 0, warnings only for unused variables,
  unused simp arguments, and unnecessary `simpa`/`decide` in earlier helper lemmas.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/FileAddress.lean -o /tmp/end-lean/Benchmarks/Dss/End/FileAddress.olean'`
  from repo root: exit 0, same warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `file(bytes32,address)`: exit 0, with the expected warning that
  `endCorrect` uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Dispatcher294343.lean -o /tmp/end-lean/Benchmarks/Dss/End/Dispatcher294343.olean'`
  from repo root after adding `endReachCage`: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Cage.lean'`
  from repo root after adding the vat-call paired refinement: exit 0, warnings only for existing
  unused simp arguments.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Cage.lean -o /tmp/end-lean/Benchmarks/Dss/End/Cage.olean'`
  from repo root: exit 0, same warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after the checked `Cage.lean` fragments: exit 0, with the expected warning that
  `endCorrect` uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Cage.lean'`
  from repo root after strengthening the vat-call success relation: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Cage.lean -o /tmp/end-lean/Benchmarks/Dss/End/Cage.olean'`
  from repo root: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/CageBody.lean'`
  from repo root after adding `endCageBodyCore`: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/CageBody.lean -o /tmp/end-lean/Benchmarks/Dss/End/CageBody.olean'`
  from repo root: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `cage()`: exit 0, with the expected warning that `endCorrect` uses
  `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Pack.lean -o /tmp/end-lean/Benchmarks/Dss/End/Pack.olean'`
  from repo root after adding `endPackBodyCore`: exit 0, warnings only for an unnecessary `simpa`
  and unused `simp` arguments.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `pack(uint256)`: exit 0, with the expected warning that `endCorrect`
  uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Cash.lean -o /tmp/end-lean/Benchmarks/Dss/End/Cash.olean'`
  from repo root after strengthening the flux-call relation and proving the post-flux suffix:
  exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/NoMatch.lean -o /tmp/end-lean/Benchmarks/Dss/End/NoMatch.olean'`
  from repo root after adding `endX_nomatch` and `endNoMatchRevert`: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring the all-selectors-miss no-match branch: exit 0, with the expected
  warning that `endCorrect` uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Dispatcher.lean -o /tmp/end-lean/Benchmarks/Dss/End/Dispatcher.olean'`
  from repo root after adding `endReachSnip`: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Dispatcher114.lean -o /tmp/end-lean/Benchmarks/Dss/End/Dispatcher114.olean'`
  from repo root after adding `endReachFree`: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Dispatcher174223.lean -o /tmp/end-lean/Benchmarks/Dss/End/Dispatcher174223.olean'`
  from repo root after adding `endReachCageIlk` and `endReachSkim`: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Dispatcher403.lean -o /tmp/end-lean/Benchmarks/Dss/End/Dispatcher403.olean'`
  from repo root after adding `endReachFlow`, `endReachSkip`, and `endReachThaw`: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/NoMatch.lean -o /tmp/end-lean/Benchmarks/Dss/End/NoMatch.olean'`
  from repo root after adding `endSelectorMiss_of_not_match`: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after splitting the remaining selectors explicitly and deriving the bottom
  all-miss proof: exit 0, with the expected warning that `endCorrect` uses `sorry`.
- After correcting the concrete selector table for `cage(bytes32)` and `free(bytes32)`, shadow-path
  checks and compiled outputs in `/tmp/end-lean` succeeded for `Common.lean`, `Trusted.lean`,
  `Dispatcher.lean`, `Dispatcher65.lean`, `Dispatcher114.lean`, `Dispatcher174223.lean`,
  `Dispatcher294343.lean`, `Dispatcher403.lean`, and `NoMatch.lean`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after correcting the selector table: exit 0, with the expected warning that
  `endCorrect` uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Free.lean -o /tmp/end-lean/Benchmarks/Dss/End/Free.olean'`
  from repo root after adding `endFreeBodyCore`: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `free(bytes32)`: exit 0, with the expected warning that
  `endCorrect` uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Flow.lean -o /tmp/end-lean/Benchmarks/Dss/End/Flow.olean > /tmp/end-flow-check.log 2>&1'`
  from repo root after adding `endFlowBodyCore`: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean > /tmp/end-correct-check.log 2>&1'`
  from repo root after wiring `flow(bytes32)`: exit 0, with the expected warning that
  `endCorrect` uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/CageIlk.lean -o /tmp/end-lean/Benchmarks/Dss/End/CageIlk.olean'`
  from repo root after adding the `spot.ilks` paired refinement: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/CageIlk.lean -o /tmp/end-lean/Benchmarks/Dss/End/CageIlk.olean'`
  from repo root after adding and repairing the `pip.read()` paired refinement: exit 0, warnings
  only for three unused `h32Par` parameters in read-memory helper lemmas.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Arithmetic.lean -o /tmp/end-lean/Benchmarks/Dss/End/Arithmetic.olean'`
  from repo root before checking the imported `Flow`/`Arithmetic` dependency chain for
  `CageIlk.lean`: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/CageIlk.lean -o /tmp/end-lean/Benchmarks/Dss/End/CageIlk.olean'`
  from repo root after adding the `wdiv` and final `tag[ilk]` storage suffix: exit 0, warnings
  only for unused `h32Par`/`y` parameters in local helper lemmas.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/CageIlk.lean -o /tmp/end-lean/Benchmarks/Dss/End/CageIlk.olean'`
  from repo root after adding staged suffix composition and `endCageIlkBodyCore`: exit 0, warnings
  only for local unused-variable/unused-`change` tactic warnings.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `cage(bytes32)`: exit 0, with the expected warning that `endCorrect`
  uses `sorry`.
- `grep -n "sorry\\|admit" Benchmarks/Dss/End/Correct.lean Benchmarks/Dss/End/CageIlk.lean`
  from workdir after wiring `cage(bytes32)`: only the four remaining `Correct.lean` selector
  placeholders were reported (`snip`, `skip`, `skim`, and `cash`); `CageIlk.lean` has no reported
  hole.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Skim.lean -o /tmp/end-lean/Benchmarks/Dss/End/Skim.olean'`
  from repo root after repairing the tag storage-ref/source-body and first `vat.ilks` setup
  fragments: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Skim.lean -o /tmp/end-lean/Benchmarks/Dss/End/Skim.olean'`
  from repo root after adding the `vat.urns` paired refinement, `urns` return `mload`
  helpers, source frames for `ink`/`art`/`owe0`, and RD helpers through both post-`urns`
  `rmul` calls: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Skim.lean -o /tmp/end-lean/Benchmarks/Dss/End/Skim.olean'`
  from repo root after adding the skim decode helpers, second vat no-code RD helper,
  post-`vat.ilks` suffix continuation, and `endSkimBodyCore`: exit 0, warnings only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `skim(bytes32,address)`: exit 0, with the expected warning that
  `endCorrect` uses `sorry`.
- `grep -n "sorry\\|admit" Benchmarks/Dss/End/Correct.lean Benchmarks/Dss/End/Skim.lean Benchmarks/Dss/End/Cash.lean`
  from repo root after wiring `skim(bytes32,address)`: only the two remaining `Correct.lean`
  selector placeholders (`snip`, `skip`) and the existing `Cash.lean` semantic bridge placeholder
  were reported. `Skim.lean` has no reported hole.
- `grep -n "#exit" Benchmarks/Dss/End/Skim.lean Benchmarks/Dss/End/Correct.lean` from repo root
  after wiring `skim(bytes32,address)`: exit 1/no matches.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/RuntimeBlocks_005.lean -o /tmp/end-lean/Benchmarks/Dss/End/RuntimeBlocks_005.olean'`
  from repo root before checking the new snip fragments: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Snip.lean -o /tmp/end-lean/Benchmarks/Dss/End/Snip.olean'`
  from repo root after adding `dog.dogIlks` decode/call-refinement fragments: exit 0, warnings
  only.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/SnipAfterYank.lean -o /tmp/end-lean/Benchmarks/Dss/End/SnipAfterYank.olean'`
  from repo root after adding the checked `vat.grab` suffix, staged external-call continuations,
  and `endSnipBodyCore`: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `snip(bytes32,uint256)`: exit 0, with the expected warning that
  `endCorrect` uses `sorry`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/SkipGrab.lean -o /tmp/end-lean/Benchmarks/Dss/End/SkipGrab.olean'`
  from repo root after splitting out the final `vat.grab` helpers: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/SkipBody.lean -o /tmp/end-lean/Benchmarks/Dss/End/SkipBody.olean'`
  from repo root after adding `endSkipBodyCore`: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring `skip(bytes32,uint256)`: exit 0.
- `grep -RIn --include='*.lean' "\\bsorry\\b\\|\\badmit\\b\\|sorryAx" Benchmarks/Dss/End`
  from repo root after wiring `skip(bytes32,uint256)`: only the remaining
  `Benchmarks/Dss/End/Cash.lean` semantic bridge placeholder was reported.
- `grep -RIn --include='*.lean' "#exit" Benchmarks/Dss/End/Skim.lean Benchmarks/Dss/End/SnipAfterYank.lean Benchmarks/Dss/End/Skip.lean Benchmarks/Dss/End/SkipAfterHope.lean Benchmarks/Dss/End/SkipAfterYank.lean Benchmarks/Dss/End/SkipGrab.lean Benchmarks/Dss/End/SkipBody.lean Benchmarks/Dss/End/Correct.lean`
  from repo root after wiring `skip(bytes32,uint256)`: exit 1/no matches.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Presence.lean -o /tmp/end-lean/Benchmarks/Dss/End/Presence.olean'`
  from repo root after adding the split semantic bridge: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Cash.lean -o /tmp/end-lean/Benchmarks/Dss/End/Cash.olean'`
  from repo root after importing `Presence.lean` and removing the cash placeholder bridge: exit 0,
  warnings only for existing linter noise in `Cash.lean`.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean'`
  from repo root after wiring the checked cash bridge: exit 0.
- `lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . Benchmarks/Dss/End/Correct.lean -o /tmp/end-lean/Benchmarks/Dss/End/Correct.olean'`
  from repo root for the final shadow-cache import target: exit 0.
- `grep -RIn --include='*.lean' "\\bsorry\\b\\|\\badmit\\b\\|sorryAx" Benchmarks/Dss/End`
  from repo root after the final bridge: exit 1/no matches.
- `grep -RIn --include='*.lean' "#exit" Benchmarks/Dss/End/Skim.lean Benchmarks/Dss/End/SnipAfterYank.lean Benchmarks/Dss/End/Skip.lean Benchmarks/Dss/End/SkipAfterHope.lean Benchmarks/Dss/End/SkipAfterYank.lean Benchmarks/Dss/End/SkipGrab.lean Benchmarks/Dss/End/SkipBody.lean Benchmarks/Dss/End/Correct.lean`
  from repo root after the final bridge: exit 1/no matches.
- `grep -RIn --include='*.lean' "#exit" Benchmarks/Dss/End/Presence.lean Benchmarks/Dss/End/Cash.lean`
  from repo root after the final bridge: exit 1/no matches.
- `printf '%s\n' 'import Benchmarks.Dss.End.Correct' '#print axioms Benchmarks.Dss.End.endContractCorrect' | lake env sh -c 'LEAN_PATH=/tmp/end-lean:$LEAN_PATH lean -R . --stdin'`
  from repo root after final shadow-cache compilation: exit 0. Non-native/non-`native_decide`
  footprint: `propext`, `Classical.choice`, `Quot.sound`, the expected EVM precompile output-size
  axioms (`ffi_sha256_output_size`, `ffi_BLAKE2Compress_output_size`, and blob output chunks for
  BN_ADD, BN_MUL, PointEval, RIP160, SNARKV), plus the accepted local selector-table axiom
  `Benchmarks.Dss.End.endRuntimeSelectorBytes_at`. The full native-decision list was written to
  `/tmp/end-axioms.log`; `grep -n "sorryAx\\|admit" /tmp/end-axioms.log` exited 1/no matches.
- `lake build Benchmarks.Dss.End.Correct` from repo root after the final bridge: exit 1 before
  proof checking because Lake tried to remove read-only artifacts under `.lake/build`
  (`Reasoning/Constructor.olean`, `Benchmarks/Dss/End/Common.olean`, and
  `Benchmarks/Dss/End/Presence.olean`).
- Completion-audit rerun after resume:
  `Presence.lean`, `Cash.lean`, and `Correct.lean` were rechecked/compiled with the shadow
  `/tmp/end-lean` path; all exited 0. `grep -RIn --include='*.lean'
  "\\bsorry\\b\\|\\badmit\\b\\|sorryAx" Benchmarks/Dss/End` and both required/wide `#exit` scans
  exited 1/no matches. The axiom audit again exited 0; filtered non-native footprint was exactly
  `propext`, `Classical.choice`, `Quot.sound`, expected EVM precompile output-size axioms, and
  `Benchmarks.Dss.End.endRuntimeSelectorBytes_at`, with no `sorryAx`/`admit` in the log. A fresh
  `lake build Benchmarks.Dss.End.Correct` again exited 1 before proof checking due to read-only
  `.lake/build` artifact removal for `Reasoning/Constructor.olean`,
  `Benchmarks/Dss/End/Common.olean`, and `Benchmarks/Dss/End/Presence.olean`.
