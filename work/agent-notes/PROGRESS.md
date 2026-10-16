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

### Continuation: recursive Lab-to-target clock transfer

- Previous goal turn was progress: committed complete encoder, trace and padded
  line bounds as 2b04d4704. Clean worktree at restart; 4.3 GiB RAM used, disk 46%.
- Added LabBound.Common with LineBound (adjacent physical PC displacement),
  NoInstall (no fetched dynamic installer), rate B L = B*(L+1)+2, and a bounded
  replacement for CompileCorrectFor/compileCorrect_step. It retains the original
  evaluator, oracle tie, compiler relation, encoder correctness and non-error
  premises. The target clock is bounded by rate times the source Lab clock.
- Adapted Asm, Control, Cbw, ShareMem and CallFfi cases plus strong clock
  induction. Dynamic Install is excluded using the explicit NoInstall premise;
  no cost or correctness conclusion is assumed for it. Ordinary calls rejected
  by the existing compiler line relation remain rejected for the same reason.
- All recursive cases and Assembly built, using only the permitted three
  axioms. Main fixes: namespace ambiguity after relocation, indentation in
  generated applications, reserved identifier prefix, and explicit post-FFI
  machine configurations so early type inference did not select the old FFI
  oracle. Original dependency files remain unchanged. Generator:
  adapt-lab-bound.py (five case modules); Common and Assembly are direct proofs.
- LabBound.riscv built: under LineBound code L and NoInstall source.code, the
  actual RISC-V target reaches the related Lab result/FFI state within
  (16*(L+1)+2)*source.clock. No identity-interference assumption is added.
- Layout.lineBound_of_lengths, noInstall_of_lines and noInstall_of_similar
  built. These reduce the two extra premises to local syntax facts and transfer
  installation absence along the existing codeSimilar relation. Initial layout
  errors were a missing LabProps namespace and induction argument order; fixed.
- Text-only inspection of all 832 fixed Padded sections finds 205,014 encoded
  lines, 904,196 encoded bytes, maximum line size 24, matching length annotations,
  and no Install token. Stored padded-layout-scan.json. This is not a Lean proof;
  if the syntax facts are certified, the Lab multiplier is 402.
- Static import traversal: Padded64 reaches 13 candidate modules / 3,775,165
  bytes; all Padded sections together reach 5,587 modules / 471,066,768 bytes.
  This is smaller than the forbidden full artifact closure but still substantial.
  Started a two-slot fixed-section pilot before attempting the complete set.
  PaddedPilot and the final computable checker are pending. Open explicit sorrys:
  none. Failed intermediate logs with error-recovery sorryAx are not validation.
- The layout checker required renaming the reserved identifier section; fixed.
  CheckLayout.programFits_spec now checks both LineBound and NoInstall from its
  Boolean test. PaddedPilot.padded64_fits passed with only propext. Pilot and
  dependency build: 1m53.06s wall, max child RSS 4,213,024 KiB, disk at most 47%.
  Sampled summed RSS peaked at 5,160,620 KiB; minimum host MemAvailable was
  25,444,532 KiB.
- Final combined LabBound/PaddedPilot audit passed in 7.37s, max child RSS
  3,861,548 KiB. All recorded main axioms are permitted. proof-checks.json and
  incremental policy-check.json updated (69 modules, 568,969 bytes, 110 distinct
  recorded theorem axiom sets); no new explicit sorry/native_decide/
  axiom declarations. No full verifier or score run was attempted.
- The whole-program line bound is still unproved: only section 64 is certified.
  Next validate a largest section's build resources, then certify all 832 using
  the local Boolean checker and assemble their syntax facts. The existing
  codeSimilar relation can transfer NoInstall to the source Lab program.
  The preceding passes and guest gas/input work bound remain necessary for a
  finite certificate; claim.json remains infinity. Open explicit sorrys: none.

## Complete padded-layout certification (in progress)

- Added a largest-section pilot, PaddedLarge.padded713_fits. Its fixed source
  declaration is 1,552,457 bytes, the largest of the 832 Padded modules. The
  limited two-slot build is still running; no success is claimed yet.
- Added optional --max-used-memory-gib to baseline-resource-run.py. It checks
  MemTotal minus MemAvailable before launch and while sampling, and terminates
  only the owned process group on a breach. Existing disk >85% guard remains.
  Validated zero-GiB preflight rejection without starting the child, propagation
  of child exit 7 at limit 24 GiB, valid resource JSON, and py_compile.
- Generated 830 additional section theorems, reusing the checked section 64
  pilot and pending section 713 pilot, plus 54 chunks and PaddedProgram. Each
  proof imports its fixed section and uses ordinary decide. The combined list
  preserves the exact section order and append tree from Metadata.LiteralFacts
  without importing that module's extra FFI/shmem proofs. These generated files
  are pending builds; proof-checks.json is not updated for them.
- Existing lineOk allows arbitrary NOP padding, so its encoding validity does
  not supply the desired maximum line length. Retain literal layout checks.
  Added a sequential chunk driver to avoid launching thousands of blocked Lean
  jobs in a single Lake invocation; the inherited limiter still permits parallel
  builds within each chunk. No full audit/verifier is planned.
- Next-pass inspection: Stack flattening charges no source clock for straight-
  line instructions/conditionals, while calls and loop reentry consume clock.
  A proposed quantitative invariant needs structural program-node counts, a
  maximum callee-body size, and spent source clock (initial minus final), not
  initial clock alone. Lean sizeOf includes numeric operands and is unsuitable
  as a useful numeric program bound. This is a plan, not a proved estimate.
- Open explicit sorrys: none. claim.json and Solution.lean remain unchanged.
- Largest-section pilot passed: 9m25.48s, peak child RSS 4,277,204 KiB;
  peak sampled group RSS 6,233,884 KiB;
  maximum host used memory 7.127 GiB;
  maximum disk usage 47%. Main theorem axioms: only propext.
  proof-checks.json now includes this successful module (70 total).
- Started complete layout build with four shared limiter slots, justified by the
  measured memory headroom, and 24 GiB / 85% stop guards. Includes StaticTarget
  (transfer static-code premise through stateRel), 54 section chunks, combined
  PaddedProgram, and PaddedRiscV (402 times Lab source clock). All but the two
  section pilots are still pending; no finite certificate is claimed.
- Checkpoint commit da09324b4 contains the largest-section proof, all generated
  layout modules (with pending status documented), generator/driver and memory
  guard. Full build remains running; do not restart it. At this checkpoint,
  StaticTarget and chunks 0–7 have completed. This certifies 118 sections in
  those chunks plus section 713 independently. record-padded-progress.py records
  only the log prefix ending at a completed END marker; the active suffix is
  excluded. All printed axiom sets in completed chunks are permitted.
- Current complete-layout process: tool session 83802, logs/padded-all.log and
  padded-all-resources.jsonl. Shared limiter directory is
  .lake/lean-limit/run-mo46tz1p (four slots). Any concurrent Lean work must reuse
  those locks through LEAN_LIMIT_REAL, LEAN_LIMIT_LOCK_DIR and LEAN_LIMIT_SLOTS,
  not launch an independent four-slot pool. Maximum sampled whole-host used
  memory so far: 6.13 GiB; disk still 47%.
- Added FlattenBound.Common/Leaves/Control and checked them. Common counts
  structural syntax nodes without literal/register magnitudes and telescopes
  spent clock across Seq. The proposed extra-clock budget is
  4*((limit+1)*(initialClock-finalClock)+nodes program). BoundedConcl retains the
  entire original flattening conclusion with this extra numerical condition.
  There is no theorem asserting this budget for all programs yet.
- Skip, Halt, Inst and Tick cases now retain their actual 0/1 extra-clock
  witnesses. The checked Seq rule composes bounded sub-runs and their clocks,
  preserving the existing full evaluator/state/install/label hypotheses. The
  rule has explicit bounded-sub-run premises; it is not a recursive all-program
  theorem. Calls, loops, conditionals, remaining leaves, static code preservation
  and the callee/body size invariant remain unfinished.
- Stack pilot fixes: removed nonexistent Mathlib.Tactic.Omega import; qualified
  StackToLab.flattenHOL and opened Backend after moving namespaces; split
  optional call/handler tuple constructors in nodes_positive. Initial failed
  logs contain Lean error-recovery sorryAx and are not accepted evidence.
  Final flatten-control-v5.log passed, 57.00s including limiter queue time, max
  individual child RSS 1,963,532 KiB. Eight printed main theorem axiom sets are
  all subsets of propext/Classical.choice/Quot.sound. The initial dependency
  build took 2m24.66s but failed on the subsequently fixed import.
- proof-checks.json now records 199 checked modules and 246 main theorem axiom
  sets. Incremental policy check covers all 960 Solver files, including pending
  generated layout modules, and passes; that is not a build or verifier claim.
  Solution.lean/claim.json remain unchanged at infinity. No full audit/verifier,
  push, PR or submission. Open explicit sorrys: none.
- Next: monitor the existing chunk build, extend the quantitative Stack
  flattening cases, then assemble its recursion with explicit static/callee-size
  invariants. The coarse syntax budget is not known to fit the final score cap;
  retain per-function costs if uniform maximum-body bounds become too loose.


### Recursive bounded Stack flattening

- Added and checked 15 further FlattenBound modules: RemainingLeaves, Guarded,
  Arithmetic, Ffi, ShMem, If, Loop, Jumps, CallTail, StateInvariant, Syntax,
  CallBudget, CallReturn, Assembly, WholeCall. The recursive theorem now covers
  all installation-free programs with explicit program/code/oracle size bounds.
  The original semantic/state/register/label guards remain in each theorem.
- Checked extra-clock budget: 4*((M+1)*(initial-final)+nodes program).
  Whole-entry execution additionally handles the return-to-halting procedure:
  ck <= 4*((M+1)*initial+2*M), Lab initial clock = initial-1+ck.
  This is not a finite guest certificate or an instantiated artifact bound.
- Successful logs (including queue/dependency time, peak child RSS KiB):
  flatten-simple 4m39.51s / 1,977,508; flatten-flow-v2 13.41s / 1,983,108;
  flatten-jumps 13.41s / 1,955,912; flatten-state 21.71s / 1,853,888;
  flatten-return-v2 40.01s / 1,987,380; flatten-assembly-v2 16.62s / 1,930,288.
  WholeCall passed in flatten-whole-v2.log (timing recorded separately below).
- Fixed failed attempts: ancestor namespace qualification, missing leaf import,
  reserved `prefix` identifier, and unconstrained source-state metavariables in
  clock arithmetic. Failed logs' recovery sorryAx are not accepted proof evidence.
  Main theorems in the successful build closure use only permitted axioms.
- Added reproducible local evidence-index and incremental Solver policy scripts.
  They do not replace the verifier. Padded checks through chunk16 have completed;
  full layout build is still running in shared four-slot pool run-mo46tz1p.
  Disk 48%; sampled available RAM approximately 25 GiB. No independent pool.
- Open explicit sorrys: none. Solution.lean/claim.json unchanged (infinity).
  No full audit/verifier, push, PR or submission. Finite K remains unfinished.
- WholeCall final build: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:29.65; Maximum resident set size (kbytes): 2022192; Exit status: 0.


### Stack-removal allocation and sequential pilot

- Committed the complete bounded flattening/whole-entry work as 0a5d88c33.
- StackRemoveBound Allocation and Free pass. Allocation's exact guarded
  statement retains extra <=1 and available space -> extra=0 for arbitrary
  counts; Free retains extra=0. Original source/output/state guards preserved.
- Space and Seq pass with resultBudget=1 for Halt, 0 otherwise. A continuing
  first run is proved to have zero extra clock, avoiding accumulation across Seq.
- Atoms, Control, Instructions, Locations, CodeBufferWrite and ShMemOp pass.
  Conditional/loop checks were started separately with the same shared limiter.
  There is no recursive whole-pass StackRemove theorem yet.
- Fixed allocation proof normalization by splitting the register lookup after
  rewriting the imported successful-chunk execution; pretty-printed equal
  match expressions were not definitionally identical after moving namespaces.
  An attempted convert tactic was unavailable in this import closure and was
  replaced with elementary rewrites/case splits. Space needed NeZero and an
  explicit Backend namespace. All failure logs are excluded from evidence.
- scan-stack-constructors.py records source hashes and text constructor counts.
  For 826 Raw and 826 Alloc numbered procedures: zero StoreConsts/Install/Alloc,
  9,933 StackAlloc occurrences. Removed has none of these. This is a text scan,
  not a kernel theorem, and excludes small runtime/bootstrap procedures.
  Generic StoreConsts has a copyLoop allowance and remains an explicit proof
  obligation unless its absence is certified for the entire code/oracle.
- Padded layout checks through chunk20 completed (21 of 54 chunks), with the
  same parent session 83802 and lock directory run-mo46tz1p. Continue, do not
  restart. Peak sampled host used RAM 6.601 GiB; maximum disk usage 48%.
- Open explicit sorrys: none. No full audit/verifier, push, PR or submission.
  Solution.lean/claim.json still infinity. The finite-K certificate is unfinished.
- remove-space-strong: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:35.34; Maximum resident set size (kbytes): 1496568; Exit status: 0.
- remove-seq: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:31.39; Maximum resident set size (kbytes): 1531004; Exit status: 0.
- remove-leaves: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:52.49; Maximum resident set size (kbytes): 1507272; Exit status: 0.
- Conditional and loop rules passed in remove-flow.log; result-dependent bounds
  survive loop reentry because continuing body runs have zero extra clock.
- remove-flow: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:29.17; Maximum resident set size (kbytes): 1599944; Exit status: 0.
- Evidence index: 447 checked modules and 536 printed main theorem axiom sets.
  Incremental Solver policy check passes; this is not official verification.


### Complete bounded StackRemove constructor and entry simulation

- Added remaining memory/store/FFI/bitmap cases, direct/raw/tail calls, returning
  calls and handlers, Safety, Call assembly and recursive Assembly. All pass.
  The theorem retains actual compiled execution and original postconditions
  with extra <=1 for Halt and extra=0 otherwise. The continuing-prefix zero
  bound prevents costs accumulating across Seq, loops and returning calls.
- Safety explicitly excludes Install and StoreConsts in the current program,
  installed code and every compile-oracle extension; stateSafe_evaluate proves
  preservation. Actual fixed guest/initial-state instantiation is still pending.
- Entry.entrySimulation and initializedEntry pass. Initialization neutrality
  comes from the existing evaluated initializer clock theorem. The actual
  initializer run and full state relation remain premises, not assumptions
  claimed true for the guest without proof.
- Failed attempts fixed ancestor namespaces for CallReturnNone/StackMemory,
  Bool.and_eq_true_iff versus the simplifier equality, and a `decide` invocation
  with free variables (replaced by simplification). Failed logs excluded.
- Started StackAllocBound.Common/Leaves (zero-extra-clock target contract and
  25 nonrecursive cases); dependency build is running in the shared limiter.
  Prepared guarded Safety and Seq/If/Loop rules; these are not yet checked.
- Open explicit sorrys: none. No full audit/verifier, push, PR or submission.
  Solution.lean/claim.json remain unchanged at infinity. Finite K unfinished.
- remove-assembly: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:51.18; Maximum resident set size (kbytes): 2364164; Exit status: 0.
- remove-entry-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:04.26; Maximum resident set size (kbytes): 2005144; Exit status: 0.


### Allocation lowering completed; constant-copy runtime stub accounted for

- StackAllocBound leaves, Seq/If/Loop, all call forms, safety preservation and
  Assembly passed in alloc-assembly-v3.log (421 jobs). zeroCompCorrect retains
  the original compiler/state contract and proves zero extra clock. Eligible
  syntax excludes Alloc, Install and StoreConsts with some stub, allowing none.
- Fixed draft errors: scoped `open Classical in` accidentally omitted the
  NeZero variable, explicit existential goals omitted ck=0, jump constructors
  needed explicit width, and a moved Pre.setVar helper needed qualified use.
  Failed logs with recovery sorryAx are excluded from accepted evidence.
- Corrected the scan to include runtime stub files. Each of Raw and Alloc has
  one StoreConsts (label 6); Removed has none. All have zero Install/heap Alloc.
  The previous <=1 StackRemove theorem excludes StoreConsts and therefore
  cannot directly instantiate the complete guest. The installed bitmap has
  4,614 words according to fixed BitmapImageFacts, so it is not empty.
- CopyEach exact index/extra-clock equality and final-index upper bound passed.
  CopyLoop's allowance <= remaining bitmap length passed in remove-copy.log.
  Every printed main axiom set is permitted. Full execution and heap assertions
  were retained. StoreConsts constructor and StackAlloc entry wrappers pending.
- All builds reuse the four-slot lock pool run-mo46tz1p under the 24 GiB host
  memory guard. Disk currently 49%; sampled host use around 5-7 GiB.
- Full padded layout driver remains live; completed through chunk29 (30/54).
- No explicit sorrys introduced. Full audit/verifier were not run. No push,
  PR or submission. Solution.lean and claim.json still claim infinity.

- StoreConsts strengthening passed in remove-store-v2.log (995 jobs), keeping
  full execution and state relation with extra <= source.bitmaps.length.
- StackAlloc entrySimulation passed in alloc-entry-v2.log (422 jobs): source
  and target entry calls use exactly the same clock and have identical FFI.
- fixed-stubs-v3.log passed (1,522 jobs): actual RawStubs eligibility, kernel
  computation of bitmap length 4,614, numeric StoreConsts specialization and
  preservation of bitmap data under an oracle adding no words. Numeric fixed
  bitmap equality remains an explicit premise of the specialization.
- FixedBitmap's first attempt exceeded default reduction depth; raised only its
  theorem's maxRecDepth. Normalized dependent result matches by cases. The
  bitmap invariant needed its oracle predicate exposed before simplification.
  Failed builds are not counted as checked evidence.
- Recorder now handles Lean's no-axioms output as an empty axiom set.
- alloc-assembly-v3: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:07.50; Maximum resident set size (kbytes): 1804676; Exit status: 0.
- alloc-entry-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:06.66; Maximum resident set size (kbytes): 1721404; Exit status: 0.
- remove-copy: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:24.31; Maximum resident set size (kbytes): 1620684; Exit status: 0.
- remove-store-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:17.79; Maximum resident set size (kbytes): 2029492; Exit status: 0.
- fixed-stubs-v3: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:13.99; Maximum resident set size (kbytes): 1509152; Exit status: 0.


### Direct-call alternative for the installed but unused copy stub

- Enhanced the reproducible text scan: both Raw and Alloc contain zero Sum.inr
  targets and zero direct/raw/jump calls or locValue references to label 6.
  This remains text evidence; the fixed-code kernel pilot is pending.
- Prepared StackRemoveDirect Safety/Assembly/Entry with explicit direct-call
  restrictions. Installed body 6 is unrestricted; every reachable call must
  avoid it. Other installed and oracle bodies must satisfy the predicate.
  The original full simulation and resultBudget bound are retained.
- Prepared CheckCode to connect the Boolean list check to sparse-tree lookup
  invariants, and Pilot for actual Raw64, Alloc64 and runtime AllocStubs.
- Initial Safety helper attempts could not unfold the recursive call predicate
  until option/target cases were exposed; the corrected build is in progress.
- Live builds: padded-all parent 890709/session 83802; remove-direct-v2/session
  61973 is finishing pilot dependencies after its Safety failure; corrected
  remove-direct-v3/session 9094 checks Entry and CheckCode separately. All share
  the same four-slot locks. No independent limiter pools were introduced.
- Padded build has completed through chunk33; peak sampled host use 6.601 GiB,
  maximum disk use 50%. Finite certificate remains unfinished, claim infinity.

- remove-direct-v3.log now passes (1,063 jobs): Safety, CheckCode, recursive
  compCorrect and initializedEntry. All printed main theorem axioms permitted.
  The <=1 bound now allows an arbitrary installed body at key 6 while proving
  that the restricted current program only looks up certified keys.
- remove-direct-pilot.log passes (1,274 jobs): actual Raw64 is StackAlloc-eligible,
  actual Alloc64 satisfies the direct-call class, and all actual AllocStubs at
  keys other than 6 satisfy it. These are kernel checks, not scan inferences.
- Started larger actual-procedure pilot 713 in session 84720, log
  remove-direct-large.log. It uses the same four-slot pool and 24 GiB guard.
  Large.lean remains pending and is excluded from checked evidence until a
  successful completed build. Full fixed-program class certification is next.
- remove-direct-v3: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:58.28; Maximum resident set size (kbytes): 2325440; Exit status: 0.
- remove-direct-pilot: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:05.18; Maximum resident set size (kbytes): 2232552; Exit status: 0.
- Latest completed padded target: END 36/57 InitECandidate.Solver.LabBound.Padded.Chunk34 325.03s. Parent/session unchanged.
- Sampled padded-run host peak 6.758 GiB; disk peak 50%.

### Fixed Raw/Alloc syntax certification and status update

- Large procedure 713 passed in remove-direct-large.log (1,273 jobs); both main axioms are propext. Recorded as successful evidence.
- Generated 824 new per-procedure checks, 52 chunks and one aggregate. Procedures 64 and 713 reuse the checked pilots. Generated full-program equality to fixed umbrella declarations is still pending.
- First chunk initially hit Lean default recursion depth at Alloc conjunction conversion. Raised chunk maxRecDepth in the generator; stack-static-pilot-v2.log passed all 1,352 jobs, including chunk0 (procedures 64–79) and StackAllocBound.CheckCode. Failed first log is not counted as successful evidence.
- Started sequential stack-static-all driver (52 chunks plus Programs), sharing run-mo46tz1p four-slot limiter and 24 GiB host guard with the existing padded driver. Uncompleted chunks are not checked claims.
- Padded driver completed through chunk35 (36/54 chunks). Disk is 50%; no full audit/verifier, external publication or submission run.
- Inspected earlier-pass witnesses: WordToStack shared-memory/raise and StackRawCall growing tail-frame optimization can need an extra clock. Recorded bounded-induction proposal in PHASE2-PLAN.md; no new theorem for those passes yet.
- User asked progress: measurement phase complete; finite proof substantially unfinished. Guest-wide gas/input potential, earlier-pass bounds and final composition remain. claim.json stays infinity. No explicit source sorrys introduced.
- remove-direct-large: Elapsed (wall clock) time (h:mm:ss or m:ss): 7:51.37; Maximum resident set size (kbytes): 4954564; Exit status: 0; sampled peak used host memory 8.311 GiB.
- stack-static-pilot-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:52.92; Maximum resident set size (kbytes): 2358088; Exit status: 0; sampled peak used host memory 5.741 GiB.

### StackRawCall bounded induction in progress

- Previous goal turn made concrete progress: first StackStatic batch passed,
  generator and driver committed, full sequential check started. Revalidated
  both live drivers (padded PID 890709 and StackStatic PID 965512).
- Added provisional StackRawCallBound modules for reserved call credits,
  optimized/standard sequences, primitive leaves, instructions, conditionals,
  loops, raw/tail/returning calls, exceptions, jumps, recursive assembly and
  actual compiled-code entry simulation. Original evaluator/state/guard
  conclusions are retained. No new explicit source sorry or axiom.
- Proposed extra bound is source.clock - post.clock; positive-clock calls
  reserve one unit so frame-growth optimization can spend it. Entry target
  clock is intended <= 2 * source clock with identical full FFI state.
- Initial Optimized pilot runs in session 79158, rawcall-optimized.log, sharing
  the existing four-slot pool. Dependencies are still compiling; these new
  Solver modules are not yet successful proof evidence. Full assembly build
  will follow this pilot. Source gas/input bound and earlier-pass work remain.
- Added record-stack-static-progress.py, which indexes only completed chunk
  logs against unchanged source hashes, excluding a running/failing suffix.
  StackStatic has completed chunks0–1 (32 procedures); padded through chunk36
  (37/54). Latest measured host use ~6.2 GiB, disk 50%.

### StackRawCall full bounded pass and entry checked

- rawcall-entry-v4.log passed all 810 jobs. All 20 new modules and 46 printed main theorem checks are covered by that successful log.
- Full compCorrect proves both actual compTop and comp executions with extra + callCredit <= source.clock - post.clock. The original entire state relation, evaluator equation and exceptional stack-space guards remain. The recursive induction covers every constructor, calls, returns, handlers and loops.
- entrySimulation derives the actual compiled-code initial relation and execution from distinct keys, sourceCode and the source run; extra <= clock - post.clock and clock + extra <= 2*clock, preserving complete FFI state. This is a clock bound for this compiler pass, not a guest-wide target step certificate.
- Corrected missing NeZero parameter and explicit width in raw-call credit; qualified a StackProps helper outside its original namespace; unfolded instruction credit and an updated-state clock projection before arithmetic. Earlier failed logs include Lean error-recovery sorryAx and are excluded from successful evidence. No explicit source sorrys or additional axioms.
- Full audit/verifier, push, PR and Yukon submission remain unrun. claim.json remains infinity. Both fixed-code batch drivers remain active under the shared four-slot pool. Disk last measured 51%; host use 5.1 GiB.
- rawcall-optimized: Elapsed (wall clock) time (h:mm:ss or m:ss): 7:21.02; Maximum resident set size (kbytes): 1562552; Exit status: 1; sampled peak used host memory 6.601 GiB.
- rawcall-entry: Elapsed (wall clock) time (h:mm:ss or m:ss): 3:04.26; Maximum resident set size (kbytes): 1889556; Exit status: 1; sampled peak used host memory 5.272 GiB.
- rawcall-entry-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:04.61; Maximum resident set size (kbytes): 1601692; Exit status: 1; sampled peak used host memory 4.950 GiB.
- rawcall-entry-v3: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:02.91; Maximum resident set size (kbytes): 1848868; Exit status: 1; sampled peak used host memory 4.603 GiB.
- rawcall-entry-v4: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:47.05; Maximum resident set size (kbytes): 1874164; Exit status: 0; sampled peak used host memory 4.419 GiB.
- Latest completed fixed batches: StackStatic chunk5 (96 procedures) and padded chunk39 (40/54 chunks). Both processes remain live.

### Word-to-Stack weighted overhead pilot

- Previous goal turn was progress: full StackRawCall and actual entry simulation
  passed, committed as 9e09ce5c6. Both existing fixed batch drivers revalidated
  live at the start of this turn (PIDs 890709 and 965512).
- Prepared WordToStackBound cost and CodeSafe predicates, preservation using
  the pinned no-Install evaluator theorem, full original simulation plus
  numerical bound, constructive one-clock ShareInst and Raise proofs,
  sequence budget arithmetic/composition and If selection. No explicit sorry.
- Proposed allowance: limit*(source.clock-post.clock)+cost(program). Cost counts
  only ShareInst/Raise, adds Seq, takes branch/continuation maxima. A source
  call/reentry decrement pays for a body bounded by limit. No installed body
  may contain Install; this explicit obligation still needs fixed-code proof.
- Reproducible text scan (scan-word-cost.py, word-cost-scan.json) of all 826
  actual optimized Word literals finds 13 ShareInst and 669 Raise, no Install
  or MustTerminate; maximum charged-leaf count is 4 in Data66. This is not a
  kernel proof. Prepared actual optimized66/713 cost/noInstall pilots.
- ShareInst/Raise pilot running in session 45024, wordstack-pilot.log, under
  existing four-slot shared pool and 24 GiB guard. New bounded modules are
  unverified until successful builds. Seq/If and literal pilots not run yet.
- Resource check before work: host used 4.1 GiB, disk 51%, 143 GiB free. No
  full verifier/audit, push, PR or submission. claim.json remains infinity.

### Word-to-Stack cost correction and current status

- The first fixed-code batch disproved the original cost <= 4 estimate for
  optimized65. Textual constructor counts undercount shared named subprograms
  when expanded; the scan is not an upper bound. Previous pilot successes did
  not establish the universal fixed-code obligation.
- Revised local cost assigns calls zero, while a recursive ceiling bounds
  every subprogram including call continuations. The proposed recursive extra
  bound is now (2*limit)*(source.clock-post.clock)+cost(program), paying for
  both a callee and its selected continuation from the source call decrement.
  The fixed ceiling <= 4 checks and full recursive theorem remain unproved.
- wordstack-weighted-v2/v3/v4 failed in cost_le_ceiling and are not verification
  evidence. v5 removes unnecessary simplification after constructor cases;
  session 42743 runs the revised cases and WordStatic.Chunk0 in the existing
  shared four-slot pool with the 24 GiB resource guard. The full WordStatic
  driver has not started. Earlier successful proof manifest entries whose
  source changed must be refreshed after a successful revised build.
- Padded and StackStatic batch logs continue advancing. End-to-end finite K,
  whole-guest source bounds, and compiler composition remain outstanding.
  claim.json remains infinity; no full verification or submission was run.

### Checked weighted Word-to-Stack loop case and expanded leaf work

- Previous goal turn made progress: corrected cost_le_ceiling and launched v5,
  then recorded the false original cost estimate and revised accounting.
- wordstack-loop.log passed 848 jobs in 13.93s, maximum process RSS 1,896,900 KiB.
  Revised Cost, generic budget arithmetic, Tick/MustTerminate and LoopBudget/Loop
  are indexed with printed axioms limited to propext, Classical.choice, Quot.sound.
  The Loop proof derives cut clock/code preservation, source-tail clock decrease,
  body and recursive simulations, and the paid recursive allowance. Full original
  result/resource clauses, including timeout, overflow and exception origin, remain.
- Prepared zero-extra-clock Control, Inst, LocValue, MoveFull, Return, Alloc, FFI
  and StoreConsts cases by extending the original constructive witnesses. The
  leaf (session 90156) and more-leaf (session 59850) builds remain active. Their
  successful individual lines are not treated as completed-build evidence yet.
- Revised v5 session 42743 is still active. Cost and several procedures/cases
  have passed; Pilot's optimized713 ceiling computation is still live. Existing
  launchers wait on their preferred shared slot while that calculation runs;
  no processes were restarted and no extra slot pool was opened.
- Prepared returning-call InductionHypotheses, bounded simulateCalleeBodyAt and
  executeReturningContinuation; session 1775, wordstack-returning-pilot.log.
  Remaining returning-call/handler assembly and full recursive pass theorem
  are not implemented. The guarded Loop case alone is not the whole theorem.
- Refreshed completed fixed batches through padded Chunk44 (45/54) and StackStatic
  Chunk12 (13/52). Both drivers remain live. Removed superseded CheckCode/Pilot/
  Raise/ShareInst evidence entries until revised successful logs can replace them.
- Incremental Solver import/token and package policy check passed. This is not
  a full verifier or audit. No explicit source sorry/admit/native_decide/axiom;
  claim.json stays infinity. No push, PR or submission. Host memory last 4.6 GiB,
  disk 52%, with all auxiliary builds sharing the original four-slot pool.

Completed-run resource records for the Word cost revision:

- wordstack-pilot: Elapsed (wall clock) time (h:mm:ss or m:ss): 11:01.45; Maximum resident set size (kbytes): 2193996; Exit status: 0; sampled host memory peak 7.568 GiB.
- word-cost-literals: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:53.64; Maximum resident set size (kbytes): 2472348; Exit status: 1; sampled host memory peak 7.176 GiB.
- word-cost-literals-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:26.40; Maximum resident set size (kbytes): 1671336; Exit status: 0; sampled host memory peak 7.246 GiB.
- wordstack-cases: Elapsed (wall clock) time (h:mm:ss or m:ss): 2:56.44; Maximum resident set size (kbytes): 2297312; Exit status: 1; sampled host memory peak 7.090 GiB.
- word-static-pilot: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:05.42; Maximum resident set size (kbytes): 1783564; Exit status: 1; sampled host memory peak 6.829 GiB.
- wordstack-weighted-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:49.92; Maximum resident set size (kbytes): 1739748; Exit status: 1; sampled host memory peak 6.590 GiB.
- wordstack-weighted-v3: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:53.49; Maximum resident set size (kbytes): 1742204; Exit status: 1; sampled host memory peak 6.268 GiB.
- wordstack-weighted-v4: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:25.81; Maximum resident set size (kbytes): 1734976; Exit status: 1; sampled host memory peak 6.273 GiB.
- wordstack-loop: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:13.93; Maximum resident set size (kbytes): 1896900; Exit status: 0; sampled host memory peak 4.834 GiB.

### Checked no-handler returning Call and started full Word literal checks

- Previous goal turn was progress: weighted Loop and Clock passed and were
  committed (2f1a148eb; resource note 58988a346). Revalidated all active drivers
  and the long-running ceiling pilot at this turn's start.
- wordstack-weighted-v5.log passed all 1007 jobs. The revised Cost, ShareInst,
  Raise, Seq, If, tail Call, buffer/register/heap leaves and first WordStatic
  chunk are now indexed against current sources. optimized713's new ceiling
  passed; earlier superseded evidence has been replaced with fresh checks.
- Started the full WordStatic driver, session 33422, word-static-all.log, 54
  targets: 52 chunks, Programs, Fixed. It shares the same four-slot pool and
  24 GiB host-memory guard. Completed through Chunk3 when last indexed.
- wordstack-leaves.log passed 958 jobs; wordstack-more.log passed 912. Control,
  Inst, LocValue, MoveFull, Return, Alloc, FFI and StoreConsts bounds are checked.
  Returning pilot wordstack-returning-pilot.log passed 951 jobs.
- wordstack-callnone-v2.log passed 972 jobs: code/clock preservation after pop;
  return and handler eligibility extraction; forgetting a bounded simulation;
  guarded returning callee and continuation simulations; restored caller
  history; source-tail clock monotonicity; complete no-handler returning Call.
  The total extra bound is (2*limit)*(source.clock-sourcePost.clock), since a
  call's local cost is zero. All original result/resource branches remain.
- Initial CallState failed on a reserved binder name, then on unfolding ceiling
  with an unknown optional handler. Explicit option cases and definitional
  changes fixed it. Failed callstate/callhistory/callnone logs are excluded from
  verification evidence; no explicit source sorrys or extra axioms were added.
- Flat/Install boundary cases are being checked in wordstack-flat.log, session
  93702. Handler-present Call, final pass induction, fixed initialization and
  whole-guest bounds remain. A finite certificate is not yet available.
- Prepared StackStatic/Fixed.lean equality and CodeSafe statements for actual
  Raw.stack and Alloc.stack, unverified. The existing stack driver snapshot has
  53 targets and does not include this new module. Inspect umbrella dependency
  costs before its later limited build; do not run the full audit/verifier.
- Latest indexed fixed batches: padded Chunk45 (46/54), StackStatic Chunk13
  (14/52), WordStatic Chunk3 (4/52). No push, PR or submission; claim stays infinity.
- wordstack-weighted-v5: Elapsed (wall clock) time (h:mm:ss or m:ss): 12:05.03; Maximum resident set size (kbytes): 11095980; Exit status: 0; sampled host memory peak 12.296 GiB.
- wordstack-leaves: Elapsed (wall clock) time (h:mm:ss or m:ss): 17:24.79; Maximum resident set size (kbytes): 1869248; Exit status: 0; sampled host memory peak 10.465 GiB.
- wordstack-more: Elapsed (wall clock) time (h:mm:ss or m:ss): 13:28.66; Maximum resident set size (kbytes): 1934428; Exit status: 0; sampled host memory peak 5.835 GiB.
- wordstack-returning-pilot: Elapsed (wall clock) time (h:mm:ss or m:ss): 7:55.81; Maximum resident set size (kbytes): 1935712; Exit status: 0; sampled host memory peak 5.690 GiB.
- wordstack-callstate: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:03.68; Maximum resident set size (kbytes): 1619136; Exit status: 1; sampled host memory peak 4.620 GiB.
- wordstack-callhistory: Elapsed (wall clock) time (h:mm:ss or m:ss): 3:04.07; Maximum resident set size (kbytes): 3004636; Exit status: 1; sampled host memory peak 5.526 GiB.
- wordstack-callhistory-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:56.76; Maximum resident set size (kbytes): 1615212; Exit status: 1; sampled host memory peak 4.876 GiB.
- wordstack-callnone: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:03.04; Maximum resident set size (kbytes): 2700004; Exit status: 1; sampled host memory peak 5.440 GiB.
- wordstack-callnone-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:50.79; Maximum resident set size (kbytes): 2027280; Exit status: 0; sampled host memory peak 4.260 GiB.


## Word-to-Stack handler and full recursive assembly

- Previous status-only turn supplied fresh build evidence: handler history had
  completed successfully. Continued the existing proof work; no goal reset.
- Flat/Install boundary cases passed (wordstack-flat.log, 830 jobs).
- HandlerHypotheses and HandlerCallee passed (wordstack-handler-callee.log,
  967 jobs); the forgetful map and both continuations passed
  (wordstack-handler-cont.log, 968 jobs). HandlerClock, HandlerBranches and
  HandlerHistory passed (wordstack-handler-history.log, 975 jobs).
- The full handler-present Call passed (wordstack-handler.log, 977 jobs).
  Both continuations retain all original source guards and resource/result
  relations. The source call decrement pays callee plus selected continuation
  local cost; each is bounded by the code/subprogram ceiling.
- Call.lean and Assembly.lean passed (wordstack-assembly.log, 1131 jobs).
  The numerical simulation is now proved for all 26 Word evaluator cases,
  including the literal four Call induction hypotheses. No assumed target run
  or remaining induction callback occurs in the assembled theorem.
- Entry.lean additionally bounds the whole entry clock by
  (2*limit+1)*source.clock and derives matching compiled result, complete FFI
  and final clock when the source post-state stays within its stack limit.
  The original Halt-2/overflow alternative is retained in compCall.
- Initial initialization build failed because moving the proof to Solver lost
  the enclosing WordToStackProofs namespace. Added its explicit open; the v2
  build checks the complete initialization and compiled-entry wrappers.
  Failed wordstack-entry.log is excluded from successful evidence.
- All completed main theorem axiom reports use only propext, Classical.choice,
  Quot.sound. No explicit source sorry/admit or new axiom was introduced.
- Ongoing fixed batches share the original four slots and 24 GiB memory guard.
  Last indexed: Padded Chunk46 (47/54), StackStatic Chunk15 (16/52),
  WordStatic Chunk9 (10/52). Fixed Word limit=4 and initial guest obligations
  remain; no finite certificate or full verification is claimed.
- wordstack-flat: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:42.98; Maximum resident set size (kbytes): 1799492; Exit status: 0; sampled host memory peak 4.121 GiB.
- wordstack-handler-callee: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:29.93; Maximum resident set size (kbytes): 1962552; Exit status: 0; sampled host memory peak 4.179 GiB.
- wordstack-handler-cont: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:16.29; Maximum resident set size (kbytes): 2000368; Exit status: 0; sampled host memory peak 4.047 GiB.
- wordstack-handler-history: Elapsed (wall clock) time (h:mm:ss or m:ss): 2:45.06; Maximum resident set size (kbytes): 2134388; Exit status: 0; sampled host memory peak 4.558 GiB.
- wordstack-handler: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:39.26; Maximum resident set size (kbytes): 1979556; Exit status: 0; sampled host memory peak 4.794 GiB.
- wordstack-assembly: Elapsed (wall clock) time (h:mm:ss or m:ss): 2:34.31; Maximum resident set size (kbytes): 1987612; Exit status: 0; sampled host memory peak 4.404 GiB.
- wordstack-entry: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:42.14; Maximum resident set size (kbytes): 2122252; Exit status: 1; sampled host memory peak 3.831 GiB.

- wordstack-entry-v2.log passed all 1350 jobs. Entry, actual initial-relation
  construction and compiledEntry are now checked. Call/Assembly axiom print
  names were qualified and rebuilt for consistent evidence indexing.
- wordstack-entry-v2: elapsed 2:54.47; peak child RSS 2,125,596 KiB;
  sampled host memory peak 4.921 GiB; exit 0. The generic entry multiplier
  2*limit+1 is proved; its use at limit 4 for the fixed guest remains conditional
  on unfinished code, initialization and source stack-space obligations.
- Refreshed completed fixed prefixes: Padded Chunk47 (48/54), StackStatic
  Chunk16 (17/52), WordStatic Chunk11 (12/52). Manifest now has 1499 modules
  and 2186 printed main facts; all recorded SHA256 values match current source.
- Incremental package/import/token policy passes with claim infinity; this is
  not comparator verification. Disk remains 53%, with about 136 GiB free.
  No push, PR, Yukon submission or full audit/verifier. No open explicit sorrys.
- Inspected the next Crep-to-Loop gap: expression comparisons have extra ticks,
  While pays condition and administrative work, and calls pay argument and
  handler work. Added the expression-first proof order to PHASE2-PLAN.md;
  no numerical Crep-to-Loop theorem has been claimed or added yet.


## Fixed Word ceiling correction and Crep-to-Loop expression work

- Previous goal turn made concrete progress: full Word-to-Stack proof and
  compiled entry were committed as 66b01bf9c. Revalidated live fixed batches
  and current resources before continuing; 16 CPUs, 3.0 GiB host memory used,
  filesystem 53% / 136 GiB free at this turn's start.
- The original WordStatic driver terminated on a real false proposition:
  ceiling optimized287.2.2 <= 4. Its successful prefix ends at Chunk12 (13/52).
  Failed suffix evidence, including recovery sorryAx, is excluded.
- Added scan-word-ceiling-dag.py to follow subprogram references in 824 named
  DAG literals. Data64/713 have different syntax and retain checked <=4 facts.
  Scan maximum is 17, with five larger-than-four procedures: 287=11, 380=7,
  387=8, 874=17, 880=9. This scanner is not trusted as a proof.
- word-ceiling-corrected.log passes all five corrected decide upper bounds,
  their no-Install facts, and CheckCodeMonotone.entriesSafe_mono (633 jobs).
  Existing <=4 lemmas remain unchanged. Five chunks use their local larger
  ceiling, while Programs/Fixed now target global 17. Thus the conditional
  entry multiplier is 35; the earlier fixed multiplier 9 is superseded.
- Added --start-chunk to the WordStatic driver and a log argument to its
  evidence recorder. Resumed at Chunk13 in word-static-v2.log, session 99237,
  using the same four-slot pool and 24 GiB host-memory guard. The original
  terminated log is preserved. The corrected Chunk13 has passed.
- Drafted CrepToLoopBound.StraightClock, ExpressionCost and ExpressionSimulation.
  Intended route: bound clock consumed by Loop code without loops/calls,
  certify that expression compilation emits one cut per source comparison,
  then bound the existing expression simulation's existential extra clock.
  These modules are still under development and not yet recorded as checked.
  Initial builds exposed tactic-pattern, Bool rewrite and projection/name
  resolution errors; failed logs are excluded. No explicit sorry/admit added.
- word-ceiling-corrected: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:02.18; Maximum resident set size (kbytes): 1872984; Exit status: 0; sampled host memory peak 3.805 GiB.

- StraightClock passed after fully qualifying Loop state-update names and
  reducing result projections. ExpressionCost passed after qualifying the
  architecture type and normalizing addition order. ExpressionSimulation
  needed a reserved identifier renamed from syntax to compiledShape.
- creploop-expression-v4.log passes all 156 jobs. Seven main facts across three
  modules are checked: cut clock budget; all straight Loop executions;
  compiler expression/list charge and eligibility; nested sequence charge;
  scalar and list expression simulation with bounded extra. Source comparison
  count is sufficient for all expression constructors, including memory loads,
  shifts and arithmetic. All original relations and guards are retained.
- Only propext, Classical.choice and Quot.sound occur in successful axiom
  reports. There are no explicit open sorry/admit declarations. Failed earlier
  logs contain Lean recovery sorryAx and are excluded from successful evidence.
- Latest indexed batches: Padded Chunk50 (51/54), StackStatic Chunk21 (22/52),
  corrected WordStatic Chunk17 (18/52). Batches remain active; claim infinity.
  Incremental policy passes; no full audit/verifier, push, PR or submission.
- creploop-straight: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:46.93; Maximum resident set size (kbytes): 1360484; Exit status: 1; sampled host memory peak 3.803 GiB.
- creploop-straight-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:22.74; Maximum resident set size (kbytes): 1368948; Exit status: 1; sampled host memory peak 4.116 GiB.
- creploop-expression: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:06.51; Maximum resident set size (kbytes): 1405748; Exit status: 1; sampled host memory peak 3.685 GiB.
- creploop-expression-v2: Elapsed (wall clock) time (h:mm:ss or m:ss): 1:51.38; Maximum resident set size (kbytes): 1532420; Exit status: 1; sampled host memory peak 4.260 GiB.
- creploop-expression-v3: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:36.56; Maximum resident set size (kbytes): 1378000; Exit status: 1; sampled host memory peak 4.025 GiB.
- creploop-expression-v4: Elapsed (wall clock) time (h:mm:ss or m:ss): 0:56.25; Maximum resident set size (kbytes): 1390220; Exit status: 0; sampled host memory peak 4.298 GiB.
- Evidence manifest: 1745 modules and 2621 main facts; all source SHA256 hashes match.

## Crep-to-Loop control flow and leaf clock costs

- Added the program local cost, recursive ceiling and code-map invariant.
  `Simulation` retains the original compiler, evaluator and all state/memory/
  globals/code/result/locals relations, adding
  `extra <= (2*limit+3)*(source.clock-post.clock) + cost program`.
- The complete Seq, Dec, If and While case proofs now build. While pays for
  the condition/body from its source-clock decrement and telescopes repeated
  iterations. Tick uses the original exact zero-offset construction.
- `LeafCost` proves the actual compiled nonrecursive/non-Tick statements are
  straight and their clock charge is at most the source program's local cost.
  The semantic leaf wrapper, full Call case and recursive assembly are being
  checked separately; these drafts are not yet indexed as proven.
- Successful check: `creploop-control-v5.log`, 178 jobs, 57.94s elapsed,
  1,428,172 KiB maximum child RSS, 4.566GiB peak host used RAM. All printed main facts have only permitted
  axioms. Same shared four-slot pool and 24GiB host-memory guard; disk 54%.
- Earlier control attempts failed on option reduction, reserved `prefix`,
  unsupported tactic `exacts`, a redundant tactic, a Nat transitivity name,
  explicit decremented-state inference, and an unconstrained budget metavariable.
  Failed logs (including Lean recovery `sorryAx`) are excluded from evidence.
  No explicit sorry/admit/axiom/native_decide was added to Solver sources.
- Revalidated all three fixed batches live. Indexed completed prefixes:
  padded Chunk52 (53/54 chunks), StackStatic Chunk24 (25/52 chunks), corrected
  WordStatic Chunk25 (through 26/52 procedure chunks, plus final aggregates).
  No final fixed-program invariant or finite certificate is claimed.

## Full recursive Crep-to-Loop bound checked

- `creploop-assembly-v2.log` succeeded (200 jobs, 58.48s elapsed,
  1,700,296 KiB child RSS, 3.577GiB peak host used RAM).
- `simulateLeaf` derives the original simulation witness bound from compiled
  straight-line charge and endpoint clock relations; it preserves every
  original memory, globals, code, locals and result conclusion.
- `simulateCall` covers both tail and returning calls, errors excluded exactly
  as in the original theorem, normal returns, matching/mismatching exception
  handlers, timeout and final FFI results. A source decrement pays callee local
  cost, handler local cost and at most three administrative cuts.
- `compileCorrect` assembles all nineteen source constructors via the actual
  evaluator induction principle, retaining literal guarded call/loop hypotheses.
  No callback simulation is left as a theorem premise. Result:
  `extra <= (2*limit+3)*(source.clock-post.clock) + cost program`, conditional
  on the code ceiling and current program ceiling, plus all original relations.
- The first assembly attempt failed only on unfolding emptyLocals clock and
  specifying the post-state of code-invariance transport. The corrected run
  prints only propext, Classical.choice and Quot.sound for all main theorems.
- Evidence manifest now has 1,970 modules / 3,031 main facts, all source hashes
  rechecked. This is incremental proof evidence, not isolated verification.
- The actual arithmetic-simplifying compiled-entry wrapper is now in progress;
  it aims for total target clock <= (2*limit+4)*source.clock. Fixed Crep ceiling,
  remaining compiler composition and guest source-clock bound remain open.

## Actual Crep compiler entry and complete padded layout

- `CrepToLoopBound.compiledEntry` passed in `creploop-entry.log` (224 jobs,
  81.65s elapsed, 1,498,804 KiB child RSS, 3.680GiB peak host used RAM).
  It uses actual compileProgHOLExact output and transports the source run
  through crepArithSimpProgCorrect. Given the original initial relations,
  distinct function names, empty source locals, entry lookup/label, code
  equalities and CodeSafe on the simplified code, it supplies target clock
  <= (2*limit+4)*source.clock, exact result mapping and full final FFI equality.
  All printed axioms are permitted. The fixed simplified code ceiling is still
  an explicit obligation, not established by the entry theorem.
- The padded driver terminated after 3:19:07 at Chunk53: it is the empty final
  append-list group, and the generator had emitted no import plus a stray
  comma in its simp list. No actual section bound failed. Corrected generator
  and empty chunk; regeneration changes no other generated source bytes.
- `padded-final.log` now succeeds (10,416 jobs, 54.01s elapsed,
  6,962,976 KiB maximum child RSS, 4.185GiB peak observed host used RAM).
  The 832 actual padded sections (IDs 0,1,2,4,5,6 and 64..889) all satisfy
  LineBound 24. Correction to the informal update: 890 is the end of the ID
  range, not the section count. All 54 chunk aggregates, fixedPaddedProgram
  layout and padded_riscv are checked with permitted axioms.
- `padded_riscv` discharges the extra static-code/layout premises and gives
  <=402*Lab source clock; the original state relation and Lab execution are
  still premises. Literal list equality to the metadata declaration and actual
  initial-state integration remain outside this result. No final certificate.
- Fixed StackStatic and corrected WordStatic batches continue under the same
  four-slot pool. Latest indexed prefixes are Stack Chunk27 (28/52) and Word
  Chunk31 (32/52). Disk now 55%, 133GiB free, safely below the 85% stop limit.
- No explicit sorry/admit/axiom/native_decide in new sources. Failed build
  recovery terms are excluded. claim.json remains infinity; no verifier, full
  audit, external submission or push was run.

## Crep simplification ceiling and fixed-code pilot

- `creploop-simplify-v4.log` passed (142 jobs, 76.16s elapsed,
  1,445,596 KiB maximum child RSS, 3.808GiB peak observed host used RAM).
  `simplifyExpCost`, `simplifyExpsCost`, `simplifyCost`, `simplifyCeiling`
  prove arithmetic simplification cannot increase the program ceiling.
  `entriesSafe_codeSafe`, `codeSafe_simplify`, `entriesSafe_simplifiedCode`
  transport list checks to the actual simplified code map. All use only
  propext and Quot.sound. Earlier attempts failed on unfolding and pattern
  branch naming; recovery sorryAx logs are excluded, no explicit sorry added.
- Added reproducible planning scan `scan-crep-ceiling-dag.py`: all 826 literal
  DAGs parsed, maximum ceiling 126 at procedure 533. Next largest is 60 at
  procedure 15. This is untrusted planning evidence, NOT a certified bound.
- `crep-static-pilot.log` is building main procedure 0 and maximum procedure
  533 against the actual fixed imports. Their dependency chains include
  frontend declaration/translation proofs; the build remains live.
- Generated ordinary `decide` checks for all 826 procedures, 52 chunks and
  the full outputs-list equality/code invariant. These generated proof scripts
  are pending Lean validation. `build-crep-static.py` and its progress recorder
  support resumable bounded chunks under the same shared resource pool. The
  full Crep batch has NOT been started while the pilot is active.
- Inspected WordToWord.Proofs.CompileSemantics: its Pancake-facing theorem
  needs no extra clock under noInstallCode/noAllocCode/noMtCode, empty stack,
  code relation/domain and GC assumptions. Started WordToWordBound.Entry to
  retain clock and stackMax in addition to result/FFI and derive code relation
  from the actual full compiler. `wordword-entry.log` is still building; no
  success is claimed for this new wrapper yet.

## Uniform-bound feasibility audit and strategy adjustment

- Reproducible `scan-flatten-nodes.py` evaluates the same syntax-node recurrence
  as FlattenBound.nodes on the 826 individual Named procedure literal DAGs.
  Stub IDs 0,1,2,4,5,6 have no individual Named files and are explicitly recorded
  as excluded; this is not a full-code upper-bound proof. Largest parsed body:
  Named713, 12,091 nodes. A corresponding kernel equality pilot is building.
- Conditional composition arithmetic yields coefficient 348,442,536,960 per
  source-clock unit for current uniform factors (Crep 256, Word 35, RawCall 2,
  flattening limit 12,091, Lab 402). Even ignoring additive costs the Yukon
  cap admits only 25,849 source-clock units. This is not a guest execution
  bound or a formally composed compiler theorem; it exposes the excessive
  slack in the uniform maximum-body route.
- Updated Phase 2 plan to pursue execution-weighted costs, beginning with
  flattening: charge actual callees/loop iterations their own work rather than
  the largest initializer's body on every source-clock decrement. Keep existing
  checked bounds as fallback/reference. Do not declare a feasible finite K from
  multiplying global ceilings. The guest gas/input work proof remains open.
- `flatten-fixed-size.log`, `wordword-entry.log`, `crep-static-pilot.log`,
  `stack-static-all.log`, and `word-static-v2.log` are targeted builds sharing
  exactly four Lean slots, not five independent slot pools. The resource guards
  remain 24GiB host RAM and 85% disk. Current disk 55%, ~132GiB free.
- Latest indexed completed prefixes: StackStatic Chunk30, WordStatic Chunk37.
  New generated Crep checks and pending wrapper/size pilots are not in the
  successful-proof manifest. No explicit sorry/admit/axiom/native_decide added.

## Execution-weighted flattening: basic blocks, sequences, and tail calls

- The whole Named713 size equality passed: 12,091 nodes. The first weighted
  initializer pilot failed because the entire procedure is not call-free:
  it has two calls and four ticks. That failed log is excluded from evidence.
- Corrected the pilot to NamedBody713_12077, its large initialization tail:
  ordinary kernel-checked decide proves 11,995 nodes and one tick. basicClock
  bounds clock consumption; basicPaid proves PaidProp 11,996 for every source
  state. The extra Lab clock is therefore <=47,984 for this actual tail run,
  conditional on the original flattening hypotheses. This is not yet a bound
  for the entire initializer or the guest.
- Straight.lean handles call-free/loop-free supported programs without a
  global code-size ceiling. Common/Sequence retain all original simulation
  payloads and add explicit credits for actual sequence sub-runs.
- Results/CallTail passed: tail-call entry carries the callee's credits with
  no additional overhead credit, because both source and target consume a
  clock. The actual findCode lookup, nonerror conditions and state/code
  relations are preserved. No maximum-callee-size premise remains.
- Returning-call, conditional and loop credit composition drafts are checking
  in flatten-weighted-control.log. They are not successful evidence yet.
- No explicit sorry/admit/axiom/native_decide was introduced. Failed Lean
  recovery terms are excluded from successful proof evidence. claim.json is
  still infinity; no full audit/verifier, network contact or submission ran.

Successful targeted build resources (wall time includes shared-slot waiting):
- flatten-fixed-size: 4:35.74; max child RSS 3374232 KiB; peak host used 5.757 GiB.
- flatten-straight: 1:27.32; max child RSS 1848076 KiB; peak host used 4.602 GiB.
- flatten-weighted-pilot-v2: 2:17.47; max child RSS 2861380 KiB; peak host used 5.111 GiB.
- flatten-weighted-tail: 1:28.59; max child RSS 1783484 KiB; peak host used 4.667 GiB.

Latest indexed fixed-code prefixes: Stack Chunk33, Word Chunk42. Other
static builds and Word optimizer entry remain live in the shared four-slot pool.
Disk is 55%, ~131 GiB free, below the required stop threshold.

## Weighted control rules and Word optimizer clock equality

- flatten-weighted-control-v2.log passed (758 jobs, 1:46.47 elapsed,
  max child RSS 1,869,368 KiB, peak host used 5.114 GiB). Returning calls
  use callee+continuation+1 credits; selected conditionals use branch+1;
  loops use body+reentry with no maximum-body factor. All printed axioms
  are permitted. The v1 failure was an identifier substitution error in the
  returning-call proof and is excluded.
- Strengthened tail calls to require work only for the actual findCode result.
  The initial source-only Work/workPaid proof passed in
  flatten-weighted-work.log (809 jobs, 1:13.84, 1,869,908 KiB max child RSS,
  4.465 GiB peak host used). The final extension adds raw calls and conditional
  procedure jumps. Its first entry build failed on an insufficiently unfolded
  getVarImm expression; the corrected v2 whole-entry build is live. Only the
  final successful log may be used to index the changed Work source.
- WordToWordBound.Entry passed in wordword-entry-v2.log (1338 jobs,
  1:02.33, 2,211,096 KiB max child RSS, 4.054 GiB peak host used).
  entryRunsAgree and compiledEntry preserve clock, result, full FFI and
  stackMax through the actual full compiler under its existing eligibility
  assumptions. The original failed log had ambiguous compile name resolution
  and a final pair equality mismatch; both were corrected, with no axiom bypass.
- This remains incremental proof work. The fixed guest's total source work,
  compiler initial relations, and final finite-K certificate remain open.
  No explicit sorry/admit/axiom/native_decide is present in new source files.

### Weighted whole-entry build completed

- flatten-weighted-entry-v2.log passed all 1363 jobs (3:04.04 elapsed,
  max child RSS 2100812 KiB, peak host used 6.591 GiB).
  This supersedes the pending status above. All 14 FlattenWeighted source
  modules are now indexed against their current hashes with permitted axioms.
- workPaid covers the explicit source-only Work rules including selected
  branches, loops, tail/return/exception calls, conditional jumps and raw calls.
  weightedCallCorrect retains the original whole-entry result/FFI obligations
  and produces an actual Lab run with extra clock <=4*(entryCredits+haltCredits).
  Its source-work premises and original state/code/result hypotheses still
  need to be established for the fixed guest. No final finite K is claimed.
- initializationTail_work constructs Work 11996 for the concrete 11,995-node,
  one-tick literal tail, independent of installed procedure sizes and clock.
- Latest indexed static prefixes: Stack Chunk35 (36/52), Word Chunk47 (48/52).
  Stack/Word/Crep static processes remain live under the shared four-slot pool.
  Disk remains 55%, ~130 GiB free. Incremental policy check passed and all
  2552 indexed source hashes matched (4173 printed axiom checks).
  No full audit/verifier, push, PR, external contact or Yukon submit was run.

## Mixed native instruction and NOP padding costs

- Identified unnecessary slack in the old 402*Lab clock result: each padding
  byte was charged at the worst-case full-instruction encoder bound 16.
- NopBound proves the restricted NOP assertion contract with one actual
  evaluator/native transition, using the existing checked Skip proof. Its
  PaddingContract also checks the four-byte NOP encoding. NopCostTight and
  LabCostTight derive the real padded-prefix witness <=bound+bytes.length/4,
  preserving memory, arbitrary interference and complete target state relations.
- The complete LabBoundTight family passed in lab-tight.log (10,428 jobs,
  mostly cached dependency replays; 3:19.15 elapsed, max child RSS 6,585,376 KiB,
  peak observed host used 5.853 GiB). padded_riscv gives <=24*Lab clock for the
  checked fixed padded program, a 16.75-fold improvement over 402. All printed
  axioms are permitted. This is an incremental targeted build, not a full audit
  or verifier run. Initial-state integration and actual Lab execution remain
  premises.
- The earlier nop-tight.log pilot passed with a weaker bytes-count bound;
  only the final current sources from lab-tight.log are indexed. The adaptation
  script adapt-lab-tight.py reproduces the full Lab case family from the checked
  prior local proofs; only cost interfaces/arithmetic changed.
- loopWorkOfRank/loopPaidOfRank passed in flatten-loop-rank.log (811 jobs,
  29.63s elapsed, 1,753,992 KiB max child RSS, 5.598 GiB peak host used).
  This gives (rank+1)*perBody credits under a genuine source body budget and
  decreasing invariant. It is not yet a guest-loop invariant. The companion
  consumed-clock rank theorem is checking in flatten-loop-clock-rank.log.
- Corrected WordStatic v2 finished all 54 targets, including the actual outputs
  equality and fixedWordCodeSafe 17. Total v2 elapsed 1:08:57, max child RSS
  4,124,344 KiB, peak observed host used 6.805 GiB. The prior failed ceiling-4
  batch remains excluded. Latest indexed Stack prefix is Chunk38 (39/52).
- Crep pilot and Stack static batch remain live in the same four-slot pool.
  claim.json remains infinity. No explicit sorry/admit/native_decide/axiom,
  network contact, full audit/verifier, push, PR or Yukon submission was added.

### Consumed-clock loop rank bound completed

- flatten-loop-clock-rank.log passed all 812 jobs (58.01s elapsed,
  max child RSS 1,758,512 KiB, peak host used 4.533 GiB).
  loopClockOfRank proves source.clock <= final.clock +
  (rank(source)+1)*(perBodyClock+1), retaining final unused clock. Together
  with loopWorkOfRank this separates source-clock and extra flattening costs.
  Neither theorem supplies the invariant for any fixed guest loop, and neither
  asserts a minimal-clock entry run. Printed axioms are permitted.
- Word static batch is complete. Stack static and Crep pilot remain live;
  no duplicate Crep batch was started while the pilot was still running.
  Disk is now 56%, ~130 GiB free; host used memory is about 3.3 GiB.
  All work remains local, claim.json infinity, and no full verification is claimed.
