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
