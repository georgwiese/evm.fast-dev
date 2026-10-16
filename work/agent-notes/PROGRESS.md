# Baseline step-count progress

## 2026-10-16: setup and source inspection

- Branch: `agent/baseline-steps`; initial checkout clean, based on `main`.
- Read AGENTS.md, CHALLENGE, SUBMISSIONS, TESTING, EEST-SPIKE,
  ALLOC-AUDIT, JOURNAL-BOUND, ENVELOPE and arena-bound.py. Did not read CLAUDE.md.
- Initial resource observation: 16 CPUs, 30 GiB RAM (26 GiB available),
  31 GiB swap, filesystem 39% used / 176 GiB available. Host is aarch64.
- Lean 4.33.1 installed. Dependencies, binutils, Spike, ELF and fixtures absent.
  Local search including hidden caches found no substitutes. No baseline run yet.
- User subsequently authorized installation: “install what you need”. Started
  apt prerequisites, pinned Spike checkout / fixture download, and compiler build
  with LAKE_ARTIFACT_CACHE=false and the two-slot limiter. Logs under `logs/`.
- Full verifier and full audit are prohibited and have not been run.
- Source finding: htab_hash XOR-folds keys, permitting constructed collisions;
  linear probing needs a worst-case bound rather than expected constant cost.
- Source finding: bootstrap ASM trace length is 23,120, whereas documented
  hardware count is 23,127. The checked evaluator theorem currently existentially
  quantifies count. These are different quantities.
- Source finding: ALLOC-AUDIT and JOURNAL-BOUND contain stale layout and trap
  classification claims. Current Observations excludes trap lengths 1,6,7 only;
  lengths 4 and 5 remain covered. Current memory contract has 29 GiB RAM.

## Open proof obligations

No new `sorry` introduced. Existing submission still claims infinity.
Outstanding: measurements, pass cost bounds, source gas/input clock bound,
composition below the Yukon numeric limit, finite certificate and axiom checks.
No isolated verification or finite-score success is claimed.

## First checked pilot and fixture preparation

- All 33,614 fixture inputs converted successfully with no selection cap.
- `ClockBounds` built with the pinned Lean and limited Lake (one slot alongside
  two compiler-build slots; observed total used RAM below 6 GiB). Build: 2.50 s,
  maximum child RSS 827,812 KiB (`clock-bounds.time`). Initial attempt failed
  because `prefix` is a Lean keyword; renamed to `prefixCost`. No sorry used.
- `prefix_within` and `transport_within` have no axioms;
  `finite_family_bound` uses only propext and Quot.sound. This is a bookkeeping
  pilot, not a quantitative compiler theorem or finite certificate.
- Added step/gas report tool; six framing/offset/count tests pass. Gas used is
  explicitly marked as the payload claim, not measured EVM execution gas.
- Generated 16 synthetic full-guest inputs, including malformed blobs up to
  the arena boundary and zero-user-gas witness/withdrawal workloads. Not run yet.
- Added TargetClock pilot for actual evaluator terminal dispatch and bounded
  prefixes; build pending. No open sorry, but not yet typechecked.
- Initial commit needed a Git author identity. Local commits use explicit
  `Codex <codex@localhost>` command-local settings; global config unchanged.
- gh fixture download failed for lack of authentication. Public HTTPS curl
  fetched the same release asset (591 MiB), then extraction/conversion succeeded.

## Installation and target-evaluator pilot

- Spike source pinned at 55b4658dbf574ba0b714083ec436ce2cb5be1998 built
  successfully with make -j4: 6m21.87s, maximum child RSS 689,984 KiB.
  Driver build succeeded. Added opt-in breakpoint minstret_delta logging;
  rebuilt successfully. Default execution/counting is unchanged.
- Compiler build restarted from completed artifacts with six slots after
  observing about 5–7 GiB total used RAM and two Lean RSS values 1.6–1.7 GiB.
  Original two-slot log retained. TargetClock used two additional limited slots.
- TargetClock built successfully (79 jobs), 3m14.95s, maximum child RSS
  2,110,584 KiB. All three main theorems print exactly the allowed standard
  three axioms. No sorry. This checks terminal clock cost and prefix transport,
  not a finite certificate.
- check_submission.py completed: ok=true, infinity, 56,831 entries,
  2,245,005,068 bytes, no errors. Structural/policy only, not proof verification.
  An earlier premature pass entry was corrected while the check was pending.
- Preprocessed source and AST hashes differ from BASELINE.json. The current
  ROM is 950,344 bytes, not historical 950,336. Actual startup pointer and
  Bookkeeping agree at 0xa0029048; inferred bootstrap RV count is 23,132.
  These checked source/artifact discrepancies mean exact historical count
  reproduction cannot be assumed for the present checkout.
- Added library diagnostic harness (not the challenge artifact), with colliding
  table keys, bitmap rebuilding and aligned/unaligned copying. Execution pending.
- Latest observed filesystem use 44%; no 85% threshold breach.

GNU time RSS figures above are the maximum individual child/process RSS, not
aggregate parallel process memory. Total-RAM snapshots are separate observations.

## Fresh executable and measurements

- Compiler six-slot continuation succeeded: 2,150 jobs, 8m12.99s, maximum
  child RSS 2,474,792 KiB. Earlier two-slot build time is additional and not
  included in this continuation's time file.
- Guest and library harness built successfully with limited Lake wrappers:
  guest 21.87s / 901,228 KiB max child RSS; harness 21.72s / 867,404 KiB.
- Guest ELF hash af59ed6b844728699f84d400c4195e3765e1829465ae1fb6b6149fa869a1215e.
  Extracted ROM equals the committed literals byte-for-byte. BASELINE.json's
  historical ELF does not match. No challenge source or fixed proof files changed.
- Full EEST run launched with 14 workers through disk/resource guard.
  This uses the same eest-run command as eest-spike-full.sh after explicit
  fixture fetching/conversion and build. Full results pending.
- All 16 whole-guest synthetic runs and 33 library diagnostic runs exited zero.
  Measurements and caveats are in PHASE1-REPORT.md and tracked small JSON summaries.
  No synthetic conformance or formal-evaluator execution is claimed.
- Measured bootstrap 23,132. Normal vs fine stepping differs by one final WFI
  retirement; repeated checks establish 48,245 vs 48,244 for empty input.
- Started a stronger encoder pilot, SkipCost: copy the pinned Skip proof locally
  and expose its actual assertion witness zero, meaning one native transition.
  Its build is pending. No sorry introduced.
- New resource wrapper samples process-group RSS (shared pages counted multiple
  times), host MemAvailable and filesystem use every five seconds and stops
  its process group above 85% disk. Smoke check passed.

## Encoder pilot refinement

- SkipCost dependency build first used two slots, then four after observing
  only 5.5 GiB whole-host use; original log/resources retained.
- First complete elaboration checked skip_encoder_exact with only the standard
  three axioms, but skip_state_one failed: a lambda annotation incorrectly
  assigned riscv_state to the time index. Lean's error recovery printed sorryAx
  for that failed theorem. This was a failed build, not an accepted proof.
  Corrected the index to Nat; retry pending. No explicit sorry was written.
- Added MemoryCost and LocCost by exposing existing witnesses in the pinned
  proofs (one memory transition and two address-load transitions). Both pending
  builds; neither is being claimed checked yet.
- Arithmetic diagnostic harness v2 built and all 42 opcode runs exited zero.
  Measured charged gas directly from EV_REGULAR_GAS_USED. Largest diagnostic
  incremental ratio: MULMOD 1493.75 Spike instructions / opcode gas (includes
  driver operand setup, excludes EVM dispatcher and its operand opcode gas).
- Full EEST has 33,613 completed outputs; final deposit-high-count case running.

### Full corpus and expanded diagnostics completed

- Full EEST run: 33,614/33,614, with 33,605 PASS(full), nine PASS(malformed),
  zero failures. Wall 10m39.17s, max child RSS 148,216 KiB. Joined fixture gas
  and counts with baseline-step-report.py into work/baseline-steps/steps-and-gas.json.
  Summary tracked as eest-summary.json. Min 48,245, max 12,288,467,579, mean
  8,980,605.947; 32,444 gas-covered records, max 4,654,270,509. Highest ratio
  5,168.308 instructions/payload gasUsed, pairing fixture 28355. GasUsed is a
  payload claim, not independent runtime gas instrumentation.
- Expanded microbench: 42 opcode cases completed, all process rc=0; measured
  function-charged gas from output, subtracted zero-iteration instructions.
  Tracked opcode-measurements.json, separate ELF hash preserved. Maximum among
  sampled MULMOD operands 1,493.75 instructions/opcode gas; this includes driver
  setup and is not a whole-transaction bound.
- Added --witness-header generator mode, using the last header of a public
  passing fixture (witness-header.hex and witness-header-source.json). Eight
  whole-guest inputs, all rc=0, failure debug byte 4. Source inspection confirms
  nodedb_build executes before empty-transaction rejection. Initial descriptions
  predicted block-hash rejection; corrected to the observed earlier check.
  Largest duplicate-code input: 885,793,643 instructions / 134,161,654 bytes.
  1,048,576 distinct 32-byte codes: 1,426,789,894 / 37,750,010 bytes. Declared gas
  zero in all. Saved witness-measurements.json. Earlier headerless synthetic
  cases fail with code 3 before witness ingestion; report now states this.
- SkipCost retry succeeded (4.44s, max child RSS 2,162,208 KiB), both printed
  main theorem axiom sets allowed. The earlier lambda annotation failure was
  corrected; there is no remaining sorryAx in a successful build.
- MemoryCost and LocCost build succeeded: 1,145 jobs including dependencies,
  four slots, wall 2m48.34s, max child RSS 3,423,000 KiB. Main theorem axioms
  exactly propext, Classical.choice, Quot.sound. Exact native costs 1 and 2.
- Rewrote PHASE1-REPORT with current measurements, artifact drift, clock mapping,
  adversarial limitations and an explicitly unproved numeric planning envelope.
  Revised Phase 2 effort estimates based on successful constructor pilots.
- Next: EncoderClock, explicit assertion-counter-to-evaluator bridge. Its build
  is running with two slots. No finite certificate and no full verification.
  Open sorry list: none in written source; pending builds are not yet verified.
- EncoderClock built successfully: 27.08s, max child RSS 2,104,752 KiB, permitted
  three axioms. RiscVEvaluatorCosts first build exposed a config eta-equivalence
  mismatch, fixed by the pinned riscvConfig_encode lemma. Retry succeeded; its
  four main theorems have only permitted axioms. No open sorry; error recovery
  sorryAx from the failed elaboration is absent from the successful retry.
- Six reporting tests passed. Resource guards: Memory/Loc sampled group RSS sum
  peaked at 10,837,048 KiB; host available never below 23,726,028 KiB; disk 45%.

### Quantitative bootstrap coverage (in progress)

- WeightedTrace.evaluator now composes exact assertion counters into a sum of
  actual evaluateTargetHOL prefix costs. Uniform bounds compose with ASM trace
  length. Retry passed in 4.64s, max child RSS 2,301,088 KiB. Initial errors were
  a zero-addition reduction and nonlinear arithmetic normalization, both fixed.
  Axioms: evaluator standard three; total_le only propext.
- Added exact-counter adaptations for integer Binop Reg/Imm, LSL immediate,
  constants, near jumps and near simple register comparisons. Retained source
  step/relation, full interference and both assertion predicates. Initial local
  let-bound counters needed dsimp before introducing the environment; corrected.
  Binop Reg/Imm and LSL builds now pass with permitted axioms.
- ConstCost retry passes with permitted axioms, including the length ≤ 6 lemma.
  Fixed a local abbreviation preventing the length rewrite and reduced a
  singleton-list goal before decision. Original branches emit 1, 2 or 6 steps.
- Added SupportedCosts, WeightedTrace and BootstrapCost. The latter copies only
  the 40 bootstrap ASM blocks into a lightweight module and checks equality to
  the first 208 literal prefix bytes. It aims to prove the 23,132-step sum and
  an evaluator theorem conditional on local ASM checks/FFI guards. These checks
  are not yet imported or discharged for the actual initial state.
- Two-slot bootstrap encoder build was stopped via its own process group
  846781 and resumed at four slots after RAM remained ~5.4 GiB, disk 45%.
  The pinned JumpStep imports Mathlib.Tactic, so this pulls a substantial new
  dependency closure. No pinned sources modified. Current build targets only
  Solver.BootstrapCost, not the full audit or certificate.
- Open explicit sorry list: none. Pending/failed elaborations are not accepted
  proofs; only the successful module builds above have been counted as checked.
- Read-only import-closure count: fixed Proofs.BootstrapTrace reaches 47,123
  candidate modules / 1,824,308,527 source bytes. New Solver.BootstrapCost reaches
  15 candidate modules / 122,217 source bytes (external dependencies excluded).
  Saved bootstrap-import-closure.json. Avoided building the fixed trace because
  its ArtifactFacts dependency approaches the prohibited full baseline build.
- With four-slot memory still ~6 GiB, stopped only owned group 850852 and resumed
  the same target with six slots. This also picks up the corrected ConstCost
  source. Disk remains 45%; resource samples saved for both continuations.
- Split the literal bootstrap encoding into BootstrapEncoding so its byte check
  can run independently of the branch library build. After removing unused
  namespace opens and renaming Lean's reserved `prefix` identifier, it builds:
  the encoder output equals the submitted prefix's first 208 bytes. Axioms are
  propext and Quot.sound. This is a kernel-checked byte equality, distinct from
  the earlier full-ROM file comparison; no execution claim follows from it alone.

### Bootstrap cost milestone checked

- The pinned JumpStep's broad Mathlib.Tactic closure contains 2,708 Mathlib
  modules. Built the cache utility with two slots and requested only that
  closure. No network artifact download was needed: 896 remaining files were
  already cached locally. Stopped owned build group 858854 before unpacking;
  cache get completed in 8.58s wall (4.389s unpack), max child RSS 843,752 KiB.
  No pinned source was changed. New solver proofs were built locally; dependency
  artifacts are ordinary mathlib cache artifacts. This is not comparator replay.
- Near jump and near simple register comparison exact cost lemmas pass. Fixed
  namespace lookup after moving them out of their original parent namespace.
  SupportedCosts.encoder, cost_le_six and trace_bound pass with permitted axioms.
- BootstrapCost final retry passed: wall 16.37s, max child RSS 5,106,900 KiB.
  The membership proof required the actual left-associated append disjunction.
  bytes_match and exact_total depend on propext/Quot.sound; evaluator depends
  only on propext/Classical.choice/Quot.sound. No error-recovery sorryAx remains.
- The checked cost is 23,132 formal steps, CONDITIONAL on the original ASM step
  checks, memory/FFI guards and initial relation. The numerical sum and ROM
  prefix equality are closed. This is not a certificate for the full guest.
- Saved proof-checks.json with hashes of all 17 new modules and printed main
  theorem axiom sets from successful builds. No sorry, native_decide or new
  axiom declarations occur in Solver sources. Submission K remains infinity.
- Static package policy check is running separately. It does not build Lean,
  audit proof axioms or perform comparator verification. No full verifier run.
- Stopped the redundant whole-tree policy rescan after 3m32.56s (max child RSS
  210,168 KiB); its per-character comment scanner rereads the fixed 2.245 GB
  library. That interrupted run has no success result. Instead, verified the
  fixed submission files are unchanged since the prior successful full policy
  check and applied the official import parser/allowlist to all 17 Solver files,
  plus current whole-package entry/size checks. Incremental result: ok=true,
  no errors, 56,846 entries, 2,245,102,181 bytes. Scope is explicit in
  policy-check.json. This is not proof verification and did not write a score.
- Final lightweight BootstrapCost closure: 16 candidate modules, 122,811 source
  bytes, all built (external dependencies omitted). Source state contains no
  open sorry. The full finite-K certificate remains unfinished; next work is
  actual startup guards, then guest-wide cost invariants/quantitative transfer.

### Continuation: discharge actual bootstrap checks

- Previous goal turn classified as progress: committed measured corpus evidence,
  exact encoder/evaluator costs, and the conditional 23,132-step bootstrap proof.
- Further static import inspection found the large closure enters via
  BootstrapCopyGuards → BaselineInstallationFacts → ArtifactFacts. The existing
  BootstrapCodeFacts, BootstrapStraightLine and BootstrapCopyTrace closures have
  respectively 246, 255 and 248 candidate modules (about 6.1–6.2 MB source).
  Reusing those ASM checks is feasible without the 47,123-module artifact build.
- Added BootstrapChecks to bridge the old run/Checked definitions to the new
  quantitative trace, reuse the actual prelude/copy-loop checks and endpoints,
  and derive static PC/domain regions. Build pending while ROM dependencies build.
- BootstrapRegion passed (two slots): static PC/domain regions and an FFI-entry
  lower bound imply the original evaluator guards. Printed axioms permitted.
- Adapted the fixed BootstrapTailChecks into Solver, replacing configuration-
  dependent guards by 32 closed domain/PC-region facts while retaining every
  original ASM step proof. Reproduction script: adapt-tail-checks.py. An initial
  greedy regex assertion failed before writing a file; corrected the generator.
- Added BootstrapMachine to relate arbitrary public-input initial states to the
  fixed ASM memory model and derive program-domain/FFI-range facts from small
  submission metadata equalities and nonwrapping MMIO offsets. Not built yet.
- Started with two Lean slots, then resumed the owned build group 873544 at four
  after measured host RAM stayed about 5.4 GiB. New target is BootstrapTailChecks;
  full audit, full verifier and artifact proof closure remain excluded.
- Open explicit sorrys: none. New modules other than BootstrapRegion are pending
  compilation and must not yet be described as checked.

### Actual startup bound checked

- BootstrapChecks and BootstrapTailChecks built successfully. Four-slot tail
  dependency build: 7m15.93s wall, max child RSS 5,032,992 KiB. Sampled summed
  process RSS peaked at 17,646,996 KiB (shared pages counted repeatedly); minimum
  host MemAvailable was 24,132,580 KiB. Disk stayed at 46%.
- BootstrapMachine needed the LabToTarget namespace, function extensionality
  for its memory domain equality, a nonshadowing MMIO membership name and a
  final arithmetic step. BootstrapStartup needed run_append in its checked
  trace composition. Intermediate failed builds contained Lean error-recovery
  sorryAx; none is accepted as evidence. Final successful log supersedes them.
- BootstrapStartup now proves the real initial machine reaches a state related
  to installedAsm after an exact 23,132-step evaluator prefix, for every public
  input and FFI state. Its only premises describe the ROM/configuration fields;
  no ASM execution, dispatch guards or initial relation remain as hypotheses.
- Final two-slot build: 7.96s wall, max child RSS 4,512,732 KiB; all four main
  BootstrapStartup axioms lists contain only propext, Classical.choice and
  Quot.sound. Logs: bootstrap-startup.log, bootstrap-startup.time. Five new
  modules bring the Solver total to 22. proof-checks.json records hashes and
  46 distinct printed theorem axiom sets from successful builds.
- Startup's candidate-only import closure is 276 modules / 6,452,842 source
  bytes, all built. Full artifact closure remains excluded. A first diagnostic
  import scanner stopped at leading block comments and undercounted 241;
  corrected whole-file import-line traversal gives the recorded 276.
- Incremental official import-parser/allowlist check and whole-tree package
  metadata checks pass. Fixed files remain unchanged since the prior full
  policy pass. This is not comparator verification and no score was written.
- Open explicit sorrys: none. Finite-K certificate remains unfinished. Next
  obligation is the guest body cost bound and its relation to gas/input/state;
  a startup prefix alone cannot justify the numerical planning envelope.

### Continuation: complete encoder coverage and compiler line costs

- Previous goal turn was progress: committed the actual bootstrap prefix and
  its checked configuration/initial-state bridge as 54b152296. Worktree was
  clean at continuation start; host used 4.3 GiB RAM, disk 46%, 16 CPUs.
- Inspection of every pinned encoder constructor found explicit small witnesses
  already constructed before existential hiding. Adapted 30 component modules
  under Solver/BoundedEncoder, retaining original hypotheses, interference and
  both assertion predicates while adding n+1 <= 16. Generator is
  adapt-bounded-encoder.py; the dependency itself remains unchanged.
- BoundedEncoder.encoder covers every HolAsm constructor (including impossible
  LongDiv via the original asmOk contradiction). It built on the first attempt:
  two slots, 1m06.13s wall, max child RSS 3,840,868 KiB. The aggregate theorem
  and every printed component use only the permitted three axioms.
- Added BoundedTrace.evaluator: any checked ordinary ASM trace has an evaluator
  prefix count between code.length and 16*code.length, with the full endpoint
  relation. Initial nil proof needed simp for 0+clock; corrected build passes.
- Added BoundedStep preserving both evaluator and findNextInterference clock
  shifts, and EncoderBound.Contract/step as the generic quantitative interface.
  BoundedStep needed the AsmSem namespace; its evaluator and 16-step contract
  now pass. No actual execution is assumed by these encoder contracts.
- NopCost adapts the original generic padding proof: n padding NOPs cost at most
  bound*n, and a padded non-call instruction costs at most bound*(bytes.length+1).
  Two arithmetic proof fixes (Nat.mul_succ orientation and distribution in the
  goal) resolved initial errors. Both main theorems now build with permitted
  axioms. Generator: adapt-nop-cost.py.
- LabCost carries these bounds through the actual compiler state relation and
  fetched line memory/encoding checks. Its dependency build is running with two
  slots; no full baseline audit or verifier is involved. Until it finishes,
  LabCost is unverified. Open explicit sorrys: none; intermediate failed logs
  containing error-recovery sorryAx are not evidence of successful proofs.
- LabCost's initial build needed an explicit Backend namespace after moving it
  out of the pinned namespace. Corrected build passed: 9.16s wall, max child RSS
  3,925,732 KiB. Its three main theorems and all new aggregate/trace/contract
  theorems print only the three permitted axioms. The first dependency run took
  1m29.80s and failed only at LabCost; it is not counted as successful validation.
- The successful encoder build sampled peak summed RSS 5,536,548 KiB and minimum
  host MemAvailable 26,447,132 KiB; final LabCost build sampled 4,332,816 KiB and
  26,984,052 KiB respectively. Disk stayed at 46%.
- Updated proof-checks.json: 58 Solver modules, 469,844 source bytes, 92 distinct
  printed theorem axiom sets. Recursive source scan finds no explicit sorry,
  native_decide or axiom declaration. Incremental policy checks pass, fixed
  submission files remain unchanged, and every recorded module has a built
  olean. This is still local Lean checking, not comparator verification.
- Open explicit sorrys: none. The 16-step bound applies to each valid ordinary
  ASM operation, not an EVM opcode or a complete guest execution. Recursive
  Lab-to-target composition, target-line size invariants (especially Install),
  preceding pass expansions and the guest gas/input potential remain open.
  claim.json remains infinity; no full certificate has been claimed or scored.

- Added the near-register comparison axiom print omitted by the generator's
  name filter, resolving its trailing-blank-line diff warning. Final aggregate
  audit build passed (lab-cost-audit.log); git diff --check is clean.
