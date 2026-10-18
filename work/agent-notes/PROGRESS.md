# Baseline step-count progress

> **AUTHORITATIVE SCOPE CORRECTION — 2026-10-17:** The user requires a reasonably tight finite runtime bound for the current, unchanged Pancake implementation on main. There is NO numerical ceiling. Stop replacement/radix refinement/candidate compilation work. The current plan at the top of bound.md supersedes historical below-Yukon-limit objectives and checklists here. Keep reusable original-program proofs; remove the authorized replacement code after dependency review, retaining history in Git. The previous 45% estimate does not measure this corrected goal.

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
composition for the unchanged implementation, a justified finite bound with no numerical ceiling, and axiom checks.
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

## Fixed-code check recovery and concrete memzero loop pilot

- Revalidated the prior status-only turn. All three old pilot/static processes
  were terminal, so no live build was restarted. Stack stopped at Chunk40's
  default heartbeat limit after completing Chunk39. Crep's first two pilots
  failed because ordinary decide could not reduce well-founded conversion/cost
  definitions, not because a ceiling counterexample was found.
- Changed the local Crep expression-cost mutual recursion to structural recursion
  and exposed the fixed structural codec equation in each static procedure proof.
  crep-static-pilot-v3.log passed all 2106 jobs, including the complete Crep entry
  proof and both pilots (0 and 533): 59.51s elapsed, max child RSS 1,679,744 KiB,
  peak observed host used 2.911 GiB. Updated the generator and started the full
  826-procedure/52-chunk Crep batch, still requiring its final Fixed aggregate.
- Stack Chunk40 now has unlimited heartbeats. The resumable driver also builds
  Fixed after Programs; its first launch (stack-static-v2.log) failed immediately
  from an argument-parsing ordering typo, corrected before the v3 launch.
  stack-static-v3.log resumed at Chunk40 and has completed through Chunk42.
  Crep has completed through Chunk2. Both share the existing four-slot limiter
  and 24-GiB host-used-memory guard; disk remains 56%.
- BasicClock now treats break/continue as clock-neutral basic constructors.
  Its module and the existing initializer Work proof rebuilt successfully, but
  the combined memzero pilot logs remain failed and are not indexed as success.
- Started an actual-code memzero byte-tail proof over Named78's body 233,
  not a replacement program. Nodes=27, syntactic ticks=2, and Work=29; the open
  proof obligation is that a continuing body preserves base/length and increments
  index under the unsigned index<length guard. Draft rank/loop theorems depend
  on that obligation. Iterations memzero-tail through v6 failed at elaboration,
  simplification or case elimination; v7 is checking. Their recovery sorryAx
  output is failed-build evidence only. No explicit sorry/admit/axiom was added,
  and these draft main theorems are not recorded as proved.
- No full audit/verifier, external contact, push, PR or Yukon submission.
  claim.json remains infinity; source whole-entry invariants remain unsolved.

### Actual memzero byte-loop rank checked

- memzero-tail-v9.log passed all 1369 jobs (11.87s elapsed, max child RSS
  2,100,944 KiB, peak host used 4.564 GiB). This supersedes the draft status above.
  MemzeroTail.body_continues proves preservation of base/length, increment of
  index and index<length for the actual body. MemzeroTailRank.body_decreases
  proves unsigned increment cannot wrap and the remaining-byte rank decreases.
  loop_work gives 29*(remaining+1) credits; loop_clock gives consumed clock
  <=3*(remaining+1). Every printed axiom is permitted. No extra memory-validity
  assumption is needed: store failure cannot satisfy continuation.
- The simplification obstacle was resolved using a sequence equation with the
  proven clock clamp removed and matching the exact BitVec byte literal in the
  store case split. v8 built the body but failed on two redundant simp calls in
  the rank arithmetic; v9 replaced those with explicit natural-number goals.
  Failed v1-v8 logs are excluded from success indexing.
- BasicClock's break/continue extension and existing initializer proof are also
  indexed from this successful combined build. All 2851 indexed source hashes
  match, with 4682 printed facts. Latest static prefixes: Stack Chunk43,
  Crep Chunk4. Both processes remain live under the shared four-slot pool.
- New work in progress: BasicTimeout/LoopTimeout prove zero final clock on a
  timeout, so a consumed-clock bound can select a concrete sufficient initial
  clock. The first BasicTimeout build failed on a missing rewrite in the sequence
  case; corrected and checking. Neither new module is yet indexed as checked.
- The memzero loop bounds are conditional on its three entry registers. Earlier
  loops, whole-procedure call/length accounting and the complete guest certificate
  remain open. claim.json is still infinity; no full verification is claimed.

### Concrete sufficient clock and equivalent bounded execution checked

- memzero-bounded.log passed all 1364 jobs: 13.05s elapsed, max child RSS
  2,083,868 KiB, peak observed host used 3.130 GiB. BasicTimeout proves a basic
  block's timeout leaves zero clock. LoopTimeout lifts that fact to loops by
  induction on source clock, and rules out timeout when the initial clock is
  strictly above the consumed-clock bound. ClockAgreement compares any two
  non-timeout runs at a common enlarged clock using the fixed evaluateAddClock
  theorem, preserving every final state field except unused clock.
- MemzeroTailClock.enough_clock checks the explicit clock
  3*(length.toNat-index.toNat+1)+1 for the actual byte tail. bounded_paid also
  provides its flattening Work/Paid witness. MemzeroTailBounded.bounded_execution
  proves that every original non-timeout run has an execution at this explicit
  budget with identical result and full state after erasing unused clock, plus
  the 29*(remaining+1) Work derivation. This closes the initial-clock gap for
  this loop only; it is still not a whole memzero/guest bound.
- Failure history: loop-timeout.log failed from ambiguous exitLoop resolution;
  memzero-clock.log and clock-agreement.log stopped at a redundant tactic in
  that helper. Qualified the Stack semantics name and removed the redundant
  split. Only the final successful memzero-bounded.log is indexed for these
  five new modules. No explicit sorry/admit/axiom or unchecked tactic added.
- All 2907 indexed module hashes match (4757 printed facts); allowed axioms only.
  Static batches remain live: Stack completed Chunk44 (45/52 overall), Crep
  completed Chunk6 (7/52). Disk 56%, ~129 GiB free; host used ~2.4 GiB.
  No full audit/verifier, external contact, push, PR or Yukon submission.

## Whole-memzero composition in progress

- Previous goal turn was progress: committed the checked byte-tail bound and
  equivalent bounded execution. Revalidated both static drivers live; neither
  was restarted. Disk remains 56%, with the shared four-slot / 24-GiB guard.
- MemzeroWord proves the actual aligned 8-byte body's register/guard outcomes;
  MemzeroWordRank uses remainingWords=(length-index)/8, proves no counter wrap
  under length.toNat+8<2^64, and shows normal exit leaves fewer than eight bytes.
  Work is 31 per iteration including a final body; consumed clock is <=3 per
  iteration. memzero-word-rank-v2.log passed (4.62s, max child RSS 2,090,524 KiB,
  peak host used 3.110 GiB). This follows failed first pilots from the exact
  BitVec literal mismatch and a missing rewrite; failed logs are not indexed.
- MemzeroQuad/QuadRank cover the actual aligned 32-byte body and loop, with
  61 credits per iteration, rank (length-index)/32, and remainder<32 on normal
  exit. The body build passed in memzero-quad.log (26.11s, 2,175,752 KiB child
  RSS, 4.223 GiB host used); its rank passed in memzero-blocks.log.
- MemzeroBytes/BytesRank cover the actual unaligned 8-byte body, including all
  eight memory stores. Generated proof splits store results in execution order:
  failure exits immediately; success supplies the next actual memory. No store
  success/domain premise is assumed. Work=85 per iteration; normal exit leaves
  fewer than eight bytes. memzero-blocks.log passed (10.91s, 2,171,600 KiB child
  RSS, 3.255 GiB host used); memzero-bytes-rank.log passed (42.92s, 2,097,200 KiB
  child RSS, 3.332 GiB host used). Generator: generate-memzero-bytes.py.
- LoopExit proves normal-exit invariant composition for actual loops. BlockBound
  packages source Work, consumed clock, normal postcondition and zero clock on
  timeout; checked seq/ite/basic/weakening rules compose these without target
  execution premises. BlockReclock supplies equivalent explicit-clock execution.
- MemzeroSuffix composes the actual unaligned loop, final byte tail and return.
  The final tail uses at most 232 credits/24 clock because its predecessor
  leaves fewer than eight bytes. Full suffix bound is
  85*(length/8+1)+245 credits, 3*(length/8+1)+27 consumed clock.
  memzero-suffix-v2.log passed (32.98s, 2,110,888 KiB child RSS, 4.847 GiB host
  used). Earlier suffix attempt failed on literal-program rewrites and a missing
  evaluate_skip rewrite; corrected, with only the final successful log indexed.
- MemzeroAligned and MemzeroEntry are now checking. Proposed complete-procedure
  bound is 61*(length/32+1)+116*(length/8+1)+270 credits and
  3*(length/32+1)+6*(length/8+1)+34 consumed clock, with one extra initial clock.
  These final two modules are not yet recorded as proved. No explicit proof
  holes, extra axioms or unchecked tactics were introduced.
- The length premise and the number of calls still need to come from actual
  guest invariants. Other guest procedures and whole-entry integration remain
  open. claim.json remains infinity; no full verification is claimed.

### Complete fixed memzero procedure checked

- memzero-entry-v2.log passed all 1375 jobs (1:09.62 elapsed, max child RSS
  2,109,104 KiB, peak observed host used 3.920 GiB). The first entry build stopped
  at an omitted C/F annotation in a branch contract; corrected before this run.
- MemzeroEntry.entryBound covers all of Named78.2, including initialization,
  optional aligned loops, unaligned stores, short byte tail and return. It
  requires the actual base/length argument registers and length.toNat+32<2^64.
  It introduces no successful-store, target-run or missing-invariant premise.
  Its actual source Work bound is 61*(length/32+1)+116*(length/8+1)+270;
  consumed clock is <=3*(length/32+1)+6*(length/8+1)+34. bounded_execution
  supplies the run with one more initial clock, preserving original result and
  the entire final state after erasing unused clock, including memory and FFI.
- MemzeroLinear proves Work<=17*length+447 and consumed clock<=length+43.
  bounded_execution_linear accepts a caller-proved maximum M with length<=M
  and M+32<2^64 and gives an equivalent actual execution at M+44 initial Stack
  clock with 17*M+447 Work credits. memzero-linear.log passed all 1376 jobs
  (18.32s elapsed, max child RSS 2,088,748 KiB, peak host used 3.229 GiB).
  These are source-clock/work statements, not a final target-step count.
- All 3188 indexed source hashes match, with 5189 printed facts and permitted
  axioms only. No explicit sorry/admit/axiom/native_decide remains in the new
  source files; failed-build recovery output is excluded from the index.
- Stack completed all 52 chunks and Programs; the final equality/code-safety
  connection to the actual fixed Raw/Alloc tables is still building. Crep has
  completed Chunk15 (16/52). Both original resumed drivers are confirmed live,
  with the same shared four-slot pool. Disk remains 56%, ~127 GiB free.
- The whole guest still needs caller length/call-count invariants, bounds for
  other work, and initial-state/compiler/target integration. claim.json remains
  infinity. No full audit/verifier, network contact, push, PR or Yukon submit.

## Stack fixed-table checks completed; gas-update invariant pilot

- Revalidated the prior turn as progress: the complete fixed memzero procedure
  and its linear caller interface are committed and checked. Both existing
  static drivers were live at the start of this turn; no duplicate was launched.
- stack-static-v3.log completed all 14 resumed targets, including all remaining
  chunks, Programs and Fixed (32:04.81 elapsed, max child RSS 5,386,096 KiB).
  All 52 chunks are now checked across the original successful prefix and v3.
  fixedRawCodeSafe/fixedAllocCodeSafe are connected to the actual fixed tables
  by rawProgram_eq_stack/allocProgram_eq_stack. All printed axioms are permitted.
  Crep checking remains live. No full verifier or audit was run.
- Inspected actual memzero callers in guest/src. Memory expansion, copy padding,
  jump-destination bitmaps, state allocation and cryptographic code all call it;
  a per-call maximum does not establish their total work. Focus moved to the
  actual charge_gas counter update (Crep output408 / Named472).
- ChargeGasTail is a draft proof for its exact post-guard suffix; first build
  failed only on the final arbitrary-address frame condition, corrected by
  introducing its non-aliasing hypotheses before simplification. ChargeGasEntry
  is now checking the whole affordable path with explicit metadata, frame,
  domain and disjointness premises. These drafts are not yet indexed as success.
  They do not claim the global guest supplies those premises or that out-of-gas
  unwinding is bounded. No explicit sorry/admit/axiom/native_decide was added.

### Actual affordable gas-charge accounting checked

- charge-gas-cost.log passed all 1360 jobs (8.64s elapsed, max child RSS
  2,129,112 KiB, peak host used 2.658 GiB). ChargeGasTail.updates proves the two
  exact memory stores and their frame condition. ChargeGasEntry.updates proves
  the complete affordable path of actual Named472.2, from metadata/global/frame
  reads through guard, gas-left subtraction, gas-used addition and return.
  ChargeGasEntry.work proves Work 49 from the real comparison selecting the
  affordable branch, without changing or bounding the unselected unwind call.
- gas-accounting.log passed all 1361 jobs (10.61s, max child RSS 2,082,600 KiB,
  peak host used 2.959 GiB). GasAccounting.Ready lists the concrete metadata,
  domain, register and non-aliasing assumptions. charge proves exact natural
  gas consumption, gas-used increment and conservation of their sum under
  amount<=gas and gas+used<2^64, plus exact two-clock consumption and Work 49.
  A positive-charge rank corollary is checked, without asserting every guest
  iteration contains a positive charge.
- Earlier charge-gas-entry.log failed from an omitted Asm namespace, a generic
  order lemma with the wrong BitVec order instance and an ambiguous shift-amount
  literal. Explicit Nat shift and toNat order facts fixed the proof. Failed logs
  are not indexed. The bounded replay wrapper initially failed from using decide
  on goals containing free variables; replaced with reflexivity/simplification
  and checking in charge-gas-bounded-v2.log.
- Added a reproducible navigation index of all 826 fixed function names, Crep
  procedure IDs, corresponding Named Stack labels and source hashes. It is not
  proof evidence. Handles multiline name literals (the initial ad-hoc search
  missed those). Relevant next mappings: frame_mem_alloc=Named71,
  memory_gas_cost=Named481, extend_memory=Named484, charge_with_memory=Named485.
- Stack resumed batch peak observed host used was 9.114 GiB, below the guard.
  The complete Stack table checks are indexed. Crep is still running, latest
  indexed prefix Chunk28 (29/52). Disk is 57%, ~127 GiB free.
- These new per-call proofs do not establish global Ready, initial gas validation,
  gas transfers/refunds, positive-charge coverage, or total memory work. Those
  remain necessary for the finite certificate. claim.json remains infinity.

### Two-clock charge replay completed

- charge-gas-bounded-v2.log passed all 1366 jobs (9.79s elapsed, max child RSS
  2,073,272 KiB, peak host used 2.735 GiB). bounded_charge gives the actual
  affordable charge_gas procedure an equivalent execution at exactly two
  initial Stack clock units and Work 49, preserving all final state fields
  apart from unused clock. It retains the concrete Ready and affordable-path
  hypotheses; it does not require a target execution or assume a small original
  source clock. Printed axioms are permitted.
- Incremental Solver policy check passed. All 3466 indexed source hashes match
  (5475 printed facts); no explicit proof holes or unchecked tactics were added.
  Crep remains live through Chunk31 (32/52). Stack is complete. Full verifier,
  full audit, external contact, push, PR and Yukon submission remain unrun.

### Actual frame allocator and scratch-arena bounds checked

- Previous goal turn was a verified wait: PID1123880 was confirmed live while
  answering the status request. This turn made new checked proof progress.
- Added FrameAllocEntry.updates for actual Named71.2 (frame_mem_alloc): both
  success guards, metadata and stack safety are explicit premises; execution
  returns the old pointer, restores the stack pointer, stores the rounded new
  frame pointer, consumes exactly four Stack clock units, preserves domain/FFI
  and changes no memory outside the frame-pointer cell and saved-return cell.
- FrameAllocCost.work proves Work 58 for that actual path, using the real
  conditionals to exclude their trapping call branches. Reproducible generator:
  python3 work/agent-notes/generate-frame-alloc-cost.py. FrameAllocBounded.Ready
  packages the ABI/domain/non-alias/guard facts; bounded_allocate gives an
  equivalent actual execution with four initial clock units and Work 58,
  preserving all final state apart from unused clock.
- FrameArena proves the request is <=12,578,816 bytes if the frame pointer and
  scratch pointer satisfy the explicit fixed arena limits and ordering. Its
  mask_toNat and rounded_bounds prove exact eight-byte rounding without wrap.
  allocate_in_arena applies these facts to actual Named71 execution: the stored
  pointer covers the request, has at most seven padding bytes, is aligned and
  remains <=scratch. These are conditional local invariants, not a proof that
  guest initialization and every call preserve the arena assumptions.
- FrameArena.bounded_memzero connects a successful allocator guard and arena
  invariant to the actual Named78 memzero summary: initial Stack clock
  12,578,860 and Work 213,840,319 suffice for that request length, preserving the
  original non-timeout result and complete final state apart from unused clock.
  These numbers are not RV64 target steps or a whole-guest K; other memory
  regions/callers remain unbounded by this theorem.
- Build command: the standard guarded shared-four-slot limited-lake invocation,
  target InitECandidate.Solver.GuestWork.FrameArena. Final frame-arena-v3.log
  passed 1386 jobs, elapsed23.05s, max child RSS2,160,404KiB, peak observed host
  used2.565GiB. Earlier frame-alloc-cost.log passed1363jobs,49.85s,
  maxchildRSS2,197,808KiB,peakhost3.480GiB. All printed axioms permitted.
- Failed attempts excluded from evidence: frame-alloc-entry.log/v2/v3 exposed
  an extra compiler word-mask operation, AndOp-vs-HAnd simplification, then
  residual stack-restoration/mask equalities. Fixed with explicit kernel facts.
  frame-arena-v2.log lacked the explicit toNat form of pointer ordering for
  omega; v3 supplies it. No explicit proof holes remain. Disabled only noisy
  unused-simp-argument lint in the generated cost proof, preserving its proof.
- Incremental policy passed. All3656 indexed source hashes match,5669 printed
  facts. Crep job PID1123880 remains live; indexed throughChunk42 (43/52).
  Disk57%,~126GiB free. Full verifier/audit, external contact and publication
  remain unrun; claim remains infinity.
- Next integration: actual extend_memory=Named484 (381 DAG definitions) has
  two memzero calls: ncap-cap after frame_mem_alloc, then expand_by regardless
  of capacity growth. The latter needs the frame length/capacity invariant;
  allocator success alone does not bound every extend_memory path. Also need
  successful-call composition, runtime unwind cost, nested releases/transfers,
  global Ready preservation, initial gas validation and positive-charge coverage.

### Crep fixed table and actual returning memzero call bounds completed

- Previous goal turn made checked progress (commit819b10f08). This turn
  completed the Crep static table and integrated actual returning calls into
  local memory-work bounds; it did not complete the whole-guest certificate.
- Confirmed original Crep driver1123880 live through the last procedure chunks,
  then confirmed it terminal after all52chunks passed and Programs failed.
  The failure was a simplifier mismatch: entriesSafe was unfolded in the goal
  but the chunk lemmas were still stated through entriesSafe. Programs and its
  generator now supply explicitly typed List.all forms of those same lemmas.
  No procedure ceiling or bound was relaxed.
- crep-static-final.log passed5362jobs, including Programs, Fixed and equality
  to the actual fixed Crep.outputs. L126 and the simplified fixed-code safety
  premise are now checked for all826procedures. This closes a static premise of
  the existing Crep->Loop entry bound (factor256); initial state, whole source
  work and cross-pass integration are still required. The original job took
  56:26.24, maxchildRSS3,659,540KiB, peak observed host used8.079GiB, ending at
  the aggregate failure. Targeted final repair took53.41s,
  maxchildRSS2,049,884KiB, peakhost2.554GiB. No Crep job remains live.
- Added NoException.noException with structural noRaise check and checked loop
  lifting. It excludes exception results for the actual local evaluator,
  including malformed registers/memory and timeouts. MemzeroCall.no_exception
  applies it to the complete fixed Named78.2. This makes the actual caller
  exception handlers unreachable without assuming a target run or omitting
  source error/timeout cases.
- Added returningCallClock and returningCallTimeout: the actual returning-call
  evaluator costs one setup clock plus callee and selected return clocks, and
  leaves zero clock on timeout given the corresponding local properties.
  These support MemzeroCall.callBound, including installed code, actual link
  register setup, callee work, normal continuation and arbitrary unreachable
  exception-handler code.
- BasicFrame.normalFrame checks a restricted integer/basic instruction fragment
  and proves normal completion preserves a protected register and code. It
  permits failed setup to stop early and requires no success/domain assumption.
  This discharges register10/11 and code preservation through actual call setup.
- ExtendMemoryCalls now covers actual Named484 call214 (capacity clearing) and
  call325 (logical-length clearing), then their complete setup blocks219/330
  and store suffixes237/354. Given actual input length<=M, M+32<2^64, registers
  10/11 and installed Named78, EACH suffix has Work<=17*M+517, consumed Stack
  clock<=M+45, and an equivalent non-timeout execution at M+46 initial clock,
  preserving the full original final state apart from unused clock. Capacity
  suffix stores EV_MEM_CAP; length suffix stores EV_MEM_LEN and returns. These
  are subprogram bounds, not a bound for full extend_memory or all its callers.
- Successful evidence: call-clock.log814jobs26.88s,RSS1,775,612KiB,
  peakhost2.762GiB; memzero-call.log1379jobs32.44s,RSS2,098,616KiB,
  peakhost2.480GiB; final extend-memory-calls-v7.log1388jobs4.89s,
  RSS2,141,020KiB, peak observed host used1.114GiB (short run, sampled guard).
  All use the standard24GiB guard and shared four-slot limiter.
- Failed logs excluded: no-exception (ambiguous exitLoop namespace); basic-frame
  throughv3 and extend-memory-calls throughv5 (Option.join/bind normalization,
  explicit store-state equality elimination, finite syntax-count normalization,
  setup-node arithmetic). Final successful log replays the corrected dependencies.
  No explicit proof holes remain; all recorded axiom sets are permitted.
- Incremental policy passed; all3810 indexed module hashes matched,5836 printed
  facts. Disk57%,~126GiB free. Full verifier/audit and external actions remain
  unrun. claim.json remains infinity.
- Next: prove the actual argument-size and saved-state transfer across the
  allocator and first memzero, then compose full extend_memory, including its
  zero-length and no-capacity-growth paths. Existing call suffix contracts have
  True as their normal postcondition: they do not yet establish frame memory,
  saved-register recovery, exact EV_MEM_LEN/CAP updates or preservation through
  nested calls. Global gas, input/state processing and all unwind paths remain.

### Complete memzero memory effect and first-call state transfer checked

- Previous goal turn made checked progress (cffc8228d). This turn strengthens
  the actual callee/caller state contracts needed for whole memory-expansion
  composition; it does not complete the finite certificate.
- LoopFrame lifts any clock-independent state observation through an actual
  loop on non-timeout exits. LocalFrame adds a structural register/code check
  including loops, word stores and byte stores. BasicFrame's primitive proof
  is now public and supports store8. MemzeroFrame applies this to actual
  Named78.2: registers1,11,24,25,26 and code are preserved on every non-timeout
  exit, including errors. Entered-register facts include actual call link setup.
- ZeroMemory.Below says every existing word remains a word with no larger
  unsigned value. Proved reflexivity, transitivity, saved-bound transfer, whole
  word zero updates and zero-byte stores for either endianness. ZeroProgram and
  ZeroStoreProgram lift these facts through actual sequences, branches, loops,
  read-only leaves and literal-zero/store pairs, including failed operations
  and exhausted clocks. These are source-evaluator theorems, not assumed memory
  specifications or target-execution premises.
- MemzeroMemory.clears now covers the COMPLETE actual Named78.2 with no initial
  register, alignment, length, domain or address-separation premise. Every
  existing word remains a word with unsigned value <= its initial value, for
  every execution (including timeouts/errors). The structural proof checks all
  14 actual zero/store pairs: four quad words, one aligned word, eight unaligned
  bytes and one tail byte, plus all surrounding control flow. Reproduce with
  python3 work/agent-notes/generate-memzero-memory.py. The generator is untrusted
  scaffolding; Lean checks each application against the immutable Named78 DAG.
- MemzeroMemory.saved_length consequently preserves a numeric upper bound on
  any saved word even if zeroing overlaps that slot. This is useful for cost
  accounting; it does not assert exact memory equality or correct application
  values after overlap.
- ExtendMemoryRestore.capacity_restore proves the actual return continuation
  NamedBody484_202 restores a bounded register11 from its saved slot, code,
  stack+24 and metadata register25 on normal completion. It requires the saved
  slot differ from the handler-metadata store; no memory-domain success premise
  is required because a failed load/store cannot complete normally.
- capacity_call_saved_length combines that continuation with the actual first
  memzero call214, real link setup, no-exception result, protected-register
  proof and whole-body memory effect. Normal completion carries the saved
  logical-extension bound through arbitrary overlapping zero writes. The
  cleared-capacity length and separately saved logical length are distinct.
- ExtendMemoryTransfer.capacity_call_bound combines cost17*clearMaximum+465,
  clockclearMaximum+44 with the new meaningful postcondition: installed
  memzero code, restored stack/metadata, and register11 <= savedMaximum.
  capacity_tail_bound proves the actual following EV_MEM_CAP store block236
  preserves this postcondition on normal completion, with Work18/clock1.
  The caller's earlier allocator/setup and complete control-flow join remain.
- Successful checks (all guarded shared-four-slot limited-lake builds):
  zero-memory-frame-v2.log1352jobs5.29s,RSS2,131,208KiB,observedhost1.416GiB;
  zero-store-program.log805jobs7.28s,RSS1,819,956KiB,observedhost1.299GiB;
  memzero-memory.log1351jobs4.69s,RSS2,088,916KiB,observedhost1.117GiB;
  extend-memory-restore-v3.log1395jobs11.35s,RSS2,136,020KiB,host1.613GiB;
  final extend-memory-transfer.log1397jobs7.29s,RSS2,143,252KiB,host1.343GiB.
  Host maxima are sampled observations, especially for the short builds.
- Excluded failed attempts: local-frame/v2 (Bool/projection normalization and
  eliminated variable names); memzero-frame and zero-memory-frame (reserved
  identifier, List membership normalization and missing NeZero parameters);
  zero-program (uninferred phantom C/F result parameters); extend-memory-restore
  (tactics running after simplification closed failed-domain branches). All are
  corrected in the successful dependency closure. No explicit proof holes.
- Incremental policy passed. All3819 indexed module hashes matched,5863 printed
  facts, all with permitted axioms. Disk57%,~126GiB free. No build is running.
  Full verifier/audit, outside-server contact, push/PR/Yukon submission remain
  unrun; claim.json remains infinity.
- Next: establish beforeCall for the actual caller save/setup and allocator
  continuation, propagate afterCall through the capacity branch, and combine
  zero-length/no-growth paths with the final call suffix. Gas-paid total work,
  global arena/ABI initialization and preservation, state/input work and runtime
  unwind costs remain open. The new memory monotonicity contract reduces saved
  length aliasing obligations; it does not discharge these whole-guest premises.

### Actual memory-expansion caller setup and final suffix checked

- ExtendMemorySetup.frame_setup checks the actual 24-byte handler-frame setup
  (NamedBody484_183). Normal completion preserves installed code, clock, domains,
  argument/metadata/heap registers and the saved logical-length word, while
  updating the stack pointer. Its explicit separation premise distinguishes
  the saved slot from the handler-metadata store.
- ExtendMemoryBlock checks actual capacity call block219 and suffix237 with a
  meaningful postcondition carrying the saved logical-length bound into reg11.
  Work bounds remain 17*clearMaximum+499 and +517, with consumed clock
  clearMaximum+44 and +45. Clear length and saved logical length remain distinct.
- ExtendMemoryLength checks the entire actual final suffix363, including its
  pointer loads and base computation, using only installed memzero code and
  reg11 <= maximum. Invalid pointer loads stop early. Work <=17*maximum+527,
  consumed clock <=maximum+46; non-timeout executions replay at maximum+47
  with the same result and complete final state apart from clock.
- Successful guarded shared-four-slot builds: extend-memory-block-v3.log,
  1399 jobs,15.64s,peak RSS2,151,724KiB; extend-memory-length.log,1398 jobs,
  4.48s,peak RSS2,122,972KiB. All main axiom prints contain only permitted axioms.
- Failed setup/block attempts (extend-memory-setup,extend-memory-block,
  extend-memory-block-v2) were excluded from evidence. Fixed ambiguous getVarImm,
  a Prop mistakenly compared to true, and domain/address hypotheses containing
  +0 that simp normalized only in the goal. No explicit proof holes remain.
- Incremental policy passed; all3822 indexed source hashes match;5870 printed
  facts. Disk57%,126GiB free. Claim remains infinity. No full verifier/audit,
  outside-server contact, push, PR or Yukon submission was performed.
- Still open: earlier caller saves/allocator-return premises, zero/no-growth
  branch joins and complete extend_memory; global ABI/arena initialization and
  preservation, gas-paid total work, input/state work and runtime unwind paths;
  whole-program compiler composition and the finite certificate.

### Complete zero/no-growth entry paths and growth suffix setup checked

- Previous turn classified as progress: committed checked handler-frame and
  final-length suffix proofs. This turn adds six checked modules.
- BlockSelected evaluates the actual conditional by branchChoice. iteCases
  supplies each branch with its selected-test hypothesis; iteSelected requires
  only the reachable branch's bound. Invalid tests fail immediately.
- BlockPrefix.basicPrefix composes the actual right-associated DAG from basic
  blocks and a bounded tail. It charges the sum of per-block nodes/ticks,
  propagates a proved normal state transition and stops on failed prefixes.
- ExtendMemoryNoGrowth covers actual capacity comparison264 and suffix364
  through the final memzero/store/return, when reg12 capacity >= reg10 next
  length. Work17*M+534, consumed clockM+47, bounded replayM+48.
- ExtendMemoryEntry extends this to COMPLETE Named484.2 for nonzero expansion
  within existing capacity: Work17*M+569, consumed clockM+50, replayM+51.
  Ready spells out entry registers, installed code, safe prologue, metadata,
  frame/length/capacity memory cells and domains, actual capacity comparison,
  and amount<=M. It is conditional on these concrete source-state premises;
  they are not yet established globally. Failed later memory operations remain
  included by the suffix bounds. Whole final state agrees apart from clock.
- ExtendMemoryZero covers COMPLETE Named484.2 with amount0 and word stack/
  metadata registers: Work21, consumed clock1, replay2. No installed callee,
  valid memory, safe-stack or valid return-location premise is needed. Stack
  overflow halts and malformed return locations are included; the actual
  zero-length path cannot continue into frame reads/allocation/memzero.
- ExtendMemoryCapacityEntry checks actual suffix248 immediately after allocator
  return. It reads the memory base, computes base+capacity and nextCapacity-
  capacity, saves next capacity, executes capacity memzero and EV_MEM_CAP store,
  and supplies the saved logical-length bound for the final suffix.
  Work17*clearMaximum+529, consumed clockclearMaximum+46. Ready explicitly
  requires the allocator-restored registers, relevant lookup cells/domains and
  bounded saved word. No domain premise for the intermediate stack save is
  needed. Handler-metadata separation and clear-length bound remain explicit.
- Successful shared-four-slot guarded builds (elapsed,peak RSS KiB,sampled
  host-used GiB): block-selected-v2 4.04s/1763788/1.113;
  extend-memory-no-growth-v2 4.61s/2113996/1.097;
  extend-memory-entry-v4 5.69s/2143628/1.598 (includes BlockPrefix);
  extend-memory-zero-v2 5.28s/2140020/1.400;
  extend-memory-capacity-entry-v2 5.40s/2157184/1.608.
- Failed attempts excluded: selected-branch rewriting and vacuous alternative;
  reserved identifier prefix and namespaced basic resolution; no-growth syntax
  node count; Bool test normalization; clock-stability structure reconstruction;
  return-match splitting; final stack/metadata lookup simplification. All were
  corrected. No explicit proof holes. Incremental policy passed,3828 indexed
  source hashes match,5887 printed permitted-axiom facts. Disk57%,126GiB free.
- Next: turn the allocator success-path proof into a composable all-clock bound
  (including insufficient-clock timeouts), then prove its actual caller setup,
  save/restore and pointer-cell separation establish CapacityEntry.Ready. Growth
  arithmetic, whole-guest ABI/arena/gas/input invariants, runtime unwind and the
  final compiler/certificate composition remain open. Claim stays infinity;
  full audit/verifier and outside-server operations remain unrun.

### Allocator all-clock and saved-state transfer checked; paused at user request

- Added FrameAllocAllClocks: actual Named71.2 Work58 under valid-call ABI and
  allocation guards for every initial clock. Below4 clock units it times out
  with zero remaining clock. Generated by generate-frame-alloc-all-clocks.py;
  emitted proofs are checked by Lean against the immutable allocator DAG.
- FrameAllocBlock provides a composable Work58/clock4 bound, exact return-or-
  timeout outcome and no-exception theorem under those guards. FrameAllocState
  preserves code, stack/metadata/heap registers, domains and FFI on non-timeout
  runs; generated by generate-frame-alloc-state.py.
- FrameAllocCall bounds actual returning allocator calls with basic return
  continuations. Actual extend_memory call134 including continuation116 has
  Work82/clock5. Entry premises describe installed code and the actual callee
  ABI after link installation; the guards are still explicit premises.
- ExtendMemoryAllocRestore checks actual continuation116: restores capacity and
  next-capacity registers, moves saved logical expansion to its next slot, and
  preserves memory outside its four writes. No domain-validity assumption is
  required for normal completion; invalid domains stop early.
- ExtendMemoryAllocTransfer connects actual call134, allocator effects, and
  continuation116. Saved capacity/next-capacity/expansion survive under explicit
  separation from the allocator pointer cell and handler-metadata write.
  Code/domains/registers and memory outside the six possible write locations
  are transferred. This is the needed basis for CapacityEntry.Ready, but that
  final predicate bridge and earlier caller setup/saves remain unfinished.
- Successful final dependency-closure build: extend-memory-alloc-transfer-v2.log,
  1379 jobs. All six new modules have permitted-axiom prints. Earlier failed
  attempts involved generated indentation, contradiction/simplification tactics,
  address cancellation and an unspecified arithmetic metavariable; corrected
  in the final successful closure. No explicit proof holes were added.
- User requested commit and stop due to credits. No build remains running.
  Claim remains infinity; no finite certificate, full verifier/audit, push,
  PR or Yukon submission. The goal is paused, not complete.

### 2026-10-16 — bounded feasibility review for the Sol handoff

- User authorized the proposed feasibility review and update of bound.md, not
  an open-ended restart of proof development. Reviewed the fixed contract,
  weighted cost interfaces, compiler initialization/semantic assembly, and
  guest parsing, gas, hash-table and state-processing paths. No Lean build,
  new Spike run, installation, network contact or submission operation.
- Decision: REVISE. The existing uniform compiler factors remain too coarse.
  The weighted route also fails a specific coarse witness-table calculation:
  Named188 raw probe body 192 has 35 nodes and 2 ticks, so Work.basic prices 37 credits;
  at 4 extra Lab clocks per credit and factor 24 to target, a triangular probe
  allowance for 3,728,269 records prices 24,686,375,150,371,392 transitions before
  the other scan, base clock or other guest work. This is an inadequate upper
  bound, NOT a runtime lower bound, constructed collision input, or proof that
  a finite certificate is impossible. Joint distinctness/bytes/multiplicity
  bounds and/or tighter cost accounting remain necessary.
- Added feasibility-budget.py and its JSON output: reproducible offline integer
  arithmetic and restricted fixed-loop syntax inspection, not a Lean proof.
  The run also rehashed all 3,834 indexed Solver modules: zero mismatches.
  No whole-review elapsed-time/RSS telemetry was collected; only read-only
  source inspection and this small Python calculation ran. At review start:
  host-used RAM 2.2 GiB, disk 57%, 126 GiB available, no active proof builds.
- Located the exact desired Named entry as FullMakeInitSemantics.s3 at
  procedure 0, not fullMakeInit's returned earlier-stage state. bound.md now
  identifies the existing assembly equalities to expose and spells out I1–I6,
  including source behavior, body replay, all state/oracle premises, halt-stub
  overhead and target/certificate assembly. They are design interfaces, not
  newly checked theorems.
- Additional findings: successful decoder guards fix the gas field at byte 474;
  actual execution-to-reader correspondence is still open. Input length is a
  64-bit reduction of arbitrary list length, so huge lengths can wrap. Six
  system calls have 180M total initial regular gas and 9,400,320 initial state
  reservoir, subject to proof of conservation/call-count invariants. Witness
  construction precedes current-payload validation and consumes no user gas.
- Sol's next task is the bounded witness-budget gate in bound.md Section 3.R4.
  Do not automatically resume local allocator work. No overall go decision,
  new proof holes or proof modules; claim remains infinity. Full verification
  remains unrun and prohibited on this host under the standing instructions.

### 2026-10-17 — resumed task; joint witness-table feasibility gate remains REVISE

- User requested completion of bound.md's entire task. Inspected the contract,
  submission/isolation requirements, existing evidence, actual source tables,
  decoder slices and fixed Named/Padded hot paths. No finite certificate was
  completed. Claim stays infinity; no candidate/proof/ROM/dependency edits,
  Lean builds, Spike runs, network contact, PR, push or submission.
- Added witness-table-budget.py and its JSON evidence. Under explicit valid,
  non-full, fixed-capacity append-only table invariants, derived on paper:
  raw occupied probes R <= D(D-1)/2; find occupied probes F <= R +
  sum_r (m_r-1)*r <= R+(N-D)*D; combined <= D(N-1). Later Q lookups cost at
  most QD occupied visits plus Q empty-slot tests; Q remains unknown.
- Derived the necessary distinct-preimage byte constraint without assuming
  Keccak injectivity/randomness: L(D)=sum_k max(0,D-sum_{j<=k}256^j), with
  4N+L(D)<=B conditional on decoder/input correspondence. Two maps need two
  namespaces; using L(D_state+D_code) would be unsound. The aggregate bound
  implemented for two namespaces conservatively adds cross-table probes.
- Stipulated literal paths through immutable Padded79/185/188 give 10 encoded
  instructions per occupied raw probe, 17/20/23/26 per aligned 32-byte memeq
  mismatch, 26 for equality, 89 per full occupied find mismatch and 83 per
  matching find. Proposed selected Named raw Work15 improves syntax price 37.
  These are unformalized inspection counts, not evaluator theorems. The
  state/ABI/alignment/memory/range/non-timeout and simulation premises remain.
- Exact dimension-relaxation maximization, B=134217712 with headers omitted:
  89F+10R gives 21004777811675496 at N=23025715,D=14060301, about 2.33 times
  Kmax before empty-slot tests, hashing, allocation or any other guest work.
  Raw Work15 alone through 4*24 prices 256942111467506400. The maximum joint
  combined-probe allowance is 356864062595716. These are failures of the
  proposed upper bound, not constructed collision inputs, runtime lower
  bounds or proofs of impossibility. The tighter numerical gate still fails.
- Validation: guarded v3 run, logs/witness-table-review-v3.log (empty stderr),
  .time (exit 0, 0.80s elapsed, 28284 KiB max individual RSS), matching
  -resources.jsonl. All 186368 small table executions, 2050048 later queries
  and 1616 independent brute-force optimizer comparisons passed. V1/V2 also
  succeeded; V3 adds the matching-find path. All 3834 indexed proof-source
  hashes matched. No new Lean proof evidence was indexed or claimed.
- Incremental check-solver-policy.py passed, including the previously unrefreshed
  allocator modules: 60687 complete-package entries, 2250063930 bytes. This is
  not a trusted axiom audit, overlay-size acceptance, build verification or
  isolated comparator replay. Host-used memory around 2.27 GiB; disk 57% used,
  126 GiB available. No heavy process was launched.
- Updated bound.md's top checklist and added Section 3.R5 with the joint
  argument, exact arithmetic, literal-path premises and remaining terms.
  Followed R4's failure/revision gate rather than resuming allocator lemmas.
  Fixed Named79/185/188/190 .olean dependencies are absent; no expensive pilot
  was launched on a failing budget. A hash-family-specific aggregate
  probe/comparison-prefix bound or a justified alternative map refinement is
  needed, followed by later-query, gas, global invariant and compiler/target
  composition proofs. Read-only nodedb maps provide a possible narrower
  implementation-refinement scope, but that design is not implemented.

### 2026-10-17 — active radix revision; user superseded bounded stop points

- Continuing toward the complete task under the user's explicit instruction to
  take charge, change the plan and remove stop points. The failing generic hash
  probe bound triggered an implementation change. Claim remains infinity;
  Solution, fixed source/library/ROM and pinned dependencies remain unchanged.
- Implemented candidate-only nodedb_build/nodedb_lookup plus an iterative stable
  radix builder. The replacement uses the original allocation sizes/order,
  compresses unary levels and keeps the last duplicate ordinal. It requires no
  cryptographic distribution assumptions. Source, offline generator, unit and
  executable checks are in witness-radix*.pnk/build-witness-radix.py and
  WitnessRadixCheck.lean; RawProgram/Program define the candidate AST in Solver.
- Checked algorithm dictionary equivalence, 257 query inspections, branch/space
  bounds, exact stable scatter with a complete frame, 769N record-pass visits,
  address disjointness, preserved non-function declarations/ABI, and actual
  empty-root lookup HOL execution. Logs: witness-radix-space-v1, scatter-v2,
  visits-v1, addressing-v1, program-v3, query-empty-v5. The core model/compact
  proofs are included in successful dependency replays.
- Latest successful build witness-radix-graph-v3 also checks byte-array key
  separation/lookup, exact shift/mask and leaf-tag arithmetic, address-level
  graph traversal, logical agenda termination/record/slot bounds, and actual
  host input/gas-reader correspondence. Explicit hypotheses remain: encoded
  graph representation, real decoder checks, copy/ownership invariants and
  allocation/no-wrap ranges. These are not whole-guest or compiled-clock proofs.
  Main axiom prints contain only propext/Classical.choice/Quot.sound. Latest
  build: exit 0, 3.27s wall; preceding failed elaborations are retained and not
  indexed. Evidence index: 3,849 modules / 5,951 printed facts (not a percentage).
- Native candidate compiles/links to a 954,448-byte development ROM. Unit tests
  of actual compiled routines pass. All 33,614 EEST cases pass: 33,605 normal,
  9 malformed, zero failures (witness-radix-eest-full-v1.log and JSON), 15:05
  elapsed, max individual child RSS 136396 KiB. Sixteen accepts separately match
  every one of 65,536 public output bytes against baseline. Spike counts and
  optional interpreter checks are regression evidence, not formal clocks.
- Optional stepped source checks: v3 passed empty/singleton/last-bit/all-equal
  cases then exhausted a too-small 1,000-iteration guard. V4 guard 10,000 passes
  remaining duplicate/reversed/long-prefix/mixed cases, exit 0, 13:28 elapsed.
  The earlier large-guard v2 was terminated without a result. AST regeneration
  --check-ast also succeeds (witness-radix-repro-v1); no source difference.
- New compiler startup headers differ. Baseline installation/23,132-step
  bootstrap premises cannot be silently reused. Bound.md R6 records the exact
  values and remaining initial reserved-page relation/artifact obligations.
  A guarded targeted compile-baseline tool build is still running to compute
  the new static stack bound; inspect it before restarting any build.
- Refreshed incremental policy: pass, 60,704 full-package entries,
  2,250,160,745 bytes. This is not an isolated trusted audit or final verifier.
  No network/PR/push/submission/full build/full verifier was performed. Host
  used memory remains below 5 GiB, disk 57%; guards retain the 24 GiB ceiling.
- Continuing with actual nonempty HOL lookup, iterative memory construction,
  original-map/private-memory refinement, new startup/compiler artifacts,
  decoder/query/global gas-work accounting, and the literal finite certificate.
  witness-radix-checkpoint.json records hashes/results without committing raw
  corpora or binaries. No finite K or official verification is claimed.

### 2026-10-17 — actual branch HOL execution and fixed memeq fast path

- Saved radix implementation checkpoint 84f3b10f4 and continued immediately.
  QueryBranchStep.branch_iteration now proves one complete actual lookup AST
  branch iteration from concrete local bindings and word/byte loads. It changes
  only node; temporary bit/digit bindings and every other state field are
  preserved. The outer while still needs its separate clock accounting.
- CompareChain/ComparePrefix prove exact early-mismatch execution and fallthrough.
  Memeq32/Entry/Memory extract the actual fixed guest memeq AST and prove its
  whole aligned 32-byte path from argument/length/mask/mapped-word premises,
  including all early mismatches and equality at every initial source clock.
  WordKeys proves four words are equal iff their 32 little-endian key bytes are
  equal. No memeq execution is assumed as an input to these theorems.
- Successful dependency closure: witness-radix-memeq32-memory-v4.log and
  compare-prefix-v1.log, exit 0. Main axiom prints use only permitted axioms.
  Failed versions preserve diagnostics and are not proof evidence. Notably,
  Flapjack's word-valued shift instance requires explicit natural shift amounts
  when matching wordShiftHOL; the checked QueryBranch source resolves that.
- Evidence index now 3,857 modules / 5,970 printed facts; incremental policy
  passes at 60,712 full-package entries and 2,250,199,617 bytes. No finite claim,
  whole-guest refinement, compiled clock bound or isolated verification yet.
- Continuing with unaligned memeq's four byte-comparison loop iterations and
  their byte-memory/lookup-leaf connection, then the iterative builder memory
  invariant and global/compiler composition. The targeted guarded compiler
  depth-tool build remains live; it is building missing pinned Flapjack proof
  dependencies, not the Solution or baseline proof library. Used RAM around
  3 GiB, disk 57%. No additional EEST rerun is justified or scheduled.

### 2026-10-17 — complete fixed comparison and actual caller connection

- Checked the actual unaligned memeq byte loop, all early returns, exact byte
  equality and complete 32-byte entry execution. MemoryBytes connects the actual
  byte helper to little-endian word views and transfers views across unchanged
  memory/domain/endian fields. MemeqMemory covers both alignment cases.
- MemeqCall proves the actual DecCall, including caller locals, continuation and
  clock restoration; MemeqEnvironment derives its callee ABI from the real code
  entry. Cost is at most four source clocks plus one call clock. These are source
  semantics results, not compiled target transition bounds.
- Successful closure witness-radix-memeq-environment-v4.log, 596 targets; main
  axiom prints use only propext/Classical.choice/Quot.sound. Evidence index now
  3,868 modules / 5,995 printed facts. Failed elaborations are not indexed.
- The previously running targeted compiler tool build and static-depth run both
  completed successfully. Candidate output: 905,572 code bytes, 4,615 bitmap
  words, static stack bound 538 words; 27.91 seconds for the targeted run.
  Baseline startup/install facts still need new candidate-specific premises.
- Continuing actual radix leaf/whole-loop execution, iterative builder memory
  refinement, original-map relation and global input/gas/compiler composition.
  Claim remains infinity, Solution unchanged, no finite certificate or isolated
  verification. No full Solution/baseline audit/verifier or external submission.

### 2026-10-17 — complete actual lookup from represented memory

- QueryLeaf/Reads/Call/Step/Iteration connect the actual candidate leaf AST to
  concrete header, key and record reads and the fixed memeq implementation.
  Both hit and miss paths return exactly, including early return behavior.
- QueryMemory states the immutable representation directly in HOL memory and
  proves preservation when memory/domain/endian fields are unchanged. QueryLoop
  includes the evaluator's actual decrement/fix-clock behavior. QueryExecution
  proves the recursive whole-loop execution, preserving all nonlocal fields.
- QueryFunction.lookup_built proves the complete literal candidate lookup body
  returns the last matching input slice or absence within 262 source clocks.
  Premises include represented memory, real headers/ABI/memeq code, byte reads,
  query range and little endian. Construction must establish those premises;
  target clock conversion and whole-guest refinement are still open.
- Successful closure witness-radix-query-function-v3.log, 606 targets, permitted
  axioms only. Evidence index 3,877 modules / 6,011 printed facts. No finite K,
  full verifier, external submission or change to fixed files/Solution/claim.
- Continuing with iterative construction's actual memory/agenda invariant and
  its relationship to the original witness maps, then global composition.

### 2026-10-17 — actual construction copy/count and word-memory scatter

- BuildProgram extracts the literal helper copy loop; BuildCopy/Rows/Loop/Post
  prove its actual execution, one source clock per ordinal, exact memory
  poststate, copied rows, outside-memory frame, final index and preserved other
  locals. Hypotheses include mapped arrays, separated source/destination words,
  no-wrap counter/row ranges and enough source clock, not assumed execution.
- CountProgram/Digit/Body/Step/Post/Loop prove the actual count pass from ordinal
  array/key-byte reads. It counts precisely the zero-bit subsequence, pays one
  source clock per ordinal, preserves every other local, and preserves every
  nonlocal field except clock. Bindings supplies reusable local restoration.
- ScatterProgram extracts the literal scatter loop and its bucket-store bodies.
  WordScatter proves exact stable partition in actual HOL word memory: the
  output memory is the two ordered filtered block writes, with a complete
  frame, under cross-bucket address separation. Whole actual scatter-loop
  execution, outer iterative agenda and constructed graph relation remain open.
- Successful closures count-copy-v1 (616 targets), scatter-program-v1 (580),
  word-scatter-v1 (593). Only permitted axioms in main theorem prints. Evidence
  index: 3,892 source hashes / 6,034 printed facts. Counts are not progress
  percentages. No finite claim, compiled-clock/whole-guest refinement or final
  verification; Solution/claim/fixed source/dependencies remain unchanged.

### 2026-10-17 — complete actual stable-scatter loop

- ScatterBucket/Body/Step prove the literal bucket store, cursor increment,
  bit selection and scoped-variable restoration from actual ordinal/key reads.
  ScatterPost/Ready transfer readable arrays/key bytes through every write,
  using explicit destination separation and mapped-cell premises.
- ScatterLoop proves complete actual execution. ScatterResult/Cursors identify
  exact word-memory scatter, one source clock per ordinal, final index/cursors
  and preservation of every other local/nonlocal field. ScatterPartition joins
  this to two exact ordered filtered block writes and the actual copy-memory
  representation. The theorem does not assume a successful execution.
- Successful closure witness-radix-scatter-partition-v1.log (625 targets), only
  permitted axioms. Evidence index: 3,901 source hashes / 6,047 printed facts.
  The three inner construction passes now have actual HOL execution summaries.
  Parent allocation/no-wrap/ownership premises, outer agenda, graph completion,
  original-map relation and whole-guest/compiler/global bound remain open.
- Continuing immediately with outer construction and its graph invariant.
  Claim remains infinity; Solution/fixed source/ROM/dependencies unchanged. No
  final verifier or external submission has run.

### 2026-10-17 — actual builder entry, empty/final transition and pending pop

- BuildEquations/Cases connect the existing compressed model to terminal,
  singleton, unary and nonempty-split cases, including last-record selection.
- BuildEntry/Initialize/InitialState prove the actual thirteen declarations
  from ABI and four header cells, exact local values and local-only restoration.
  BuildEmpty proves the complete actual empty helper: only the root-zero store,
  no source-clock consumption, with every nonlocal state field accounted for.
- TerminalProgram/Reads/Finish/LoopFinish prove the actual terminal tag store
  and final return from depth zero, including final outer-loop payment of one
  source clock. StateSteps provides actual assignment/sequence clock equations.
- PopProgram/Reads/Parent/Body prove the complete actual pending-task pop from
  three suffix cells and the saved parent's bit word. It updates only depth,
  start, count, bit and dest, restores scoped parent and returns continue with
  no memory/clock change. BindingLookup supplies exact local-update facts.
- Successful closures build-cases-v2 (481), terminal-loop-finish-v2 (602),
  pop-body-v1 (586 targets). Main axiom prints contain only permitted axioms.
  Evidence index: 3,917 source hashes / 6,073 printed facts.
- Continuing with leaf-store/pop composition, unary/split/push execution and
  the full agenda/partial-graph memory invariant. Global original-map, input/gas,
  compiler/target composition and finite certificate are still open. Claim is
  infinity; no fixed files/Solution/claim changes, full verifier or submission.

### 2026-10-17 — complete terminal continuation and unary outer iteration

- PopStoreFrame/TerminalContinue protect the suffix/parent reads through the
  terminal leaf store using four explicit word-separation facts. The complete
  terminal code stores the tag, pops the next task and restores ordinal/parent
  scopes. TerminalLoopContinue proves exact actual outer-while resumption after
  its one clock payment, including fix_clock behavior.
- ScopedFrame proves exact two-temporary restoration from preserved remaining
  bindings and nonlocal fields. UnaryProgram/Body/Count/Loop use the real count
  pass and actual AST to prove a full unary outer iteration: memory unchanged,
  only bit and clock change, both temporary counters restored, exact source
  payment input.length + 1, then actual while resumption.
- Successful closure witness-radix-outer-transitions-v1.log (636 targets), only
  permitted axioms. Evidence index: 3,925 source hashes / 6,082 printed facts.
  Continuing split/push execution and the partial-graph/agenda invariant; no
  finite claim, target-clock or whole-guest refinement has been established.

### 2026-10-17 — branch allocation/push and complete sorting prefix

- SplitProgram extracts the literal split/reset/scatter/copy/allocation scopes.
  AllocationBody/Code prove the seven actual word stores, five persistent local
  updates and captured-node restoration, at every source clock. AllocationPost
  gives local/nonlocal frames; WordWrites/AllocationMemory identify all stored
  words under explicit distinct destinations and preserve every outside word.
- CopyIntervals/PartitionRows connect contiguous filtered blocks to the actual
  readable backup interval, using mapped rows, no-wrap bounds and separation.
  SortProgram/Scatter/Copy/Properties/Execution prove both actual index resets
  plus full stable scatter/copy before arbitrary continuation. The exact post
  memory writes backup and primary intervals; source-clock payment is twice
  input.length; final i and all other non-cursor locals are accounted for.
- Successful closure witness-radix-sort-allocation-checkpoint-v1.log (645
  targets), main axioms only permitted. Evidence index 3,937 source hashes /
  6,103 printed facts. No finite K or compiled/whole-guest refinement yet.
- Continuing surrounding cursor/count scope composition and the full split
  outer iteration, then agenda/partial-graph completion. Existing whole-guest
  original-map, input/gas and compiler/target obligations remain open.

### 2026-10-17 — complete split outer iteration and concrete subtree frames

- SplitScopeInputs/State/Execution compose the actual two cursor declarations,
  full sorting prefix and allocation continuation, then restore both cursors.
  SplitCountInputs/Execution derives the non-unary test from strict partition
  bounds, executes the count pass and restores zeros/i around the whole split.
  SplitLoop proves actual outer-while resumption and exact 3*input.length + 1
  source clocks. All ABI, ownership, mapped-address and no-wrap premises remain
  explicit; constructing their global invariant is the next parent obligation.
- MemoryAgreement and QueryFootprint prove lookup representation preservation
  from equality on concrete recursively read words, including aligned key-byte
  cells, without requiring equality of the whole heap. This supplies the frame
  needed while construction writes another branch or array interval.
- Successful closures split-loop-memory-v1 (656 targets) and query-footprint-v1
  (606 targets), only permitted axioms. No finite score, target-step theorem or
  whole-guest refinement is claimed. Continuing agenda/partial-graph completion.

### 2026-10-17 — partial graph, physical push and child ownership

- OpenGraph/Replace/Frontier model mapped holes and installed subtrees in actual
  HOL memory. Checked replacement preserves expected trees and represented
  ancestors/siblings; filling the first hole preserves pending order; an empty
  frontier supplies exactly the representation used by lookup.
- SplitGraph/Fill connects the actual split execution to a branch-hole fill
  and its outside-memory frame. LeafGraph installs the real ordinal key/slice
  at a leaf. OrdinalTree proves terminal/unary/split equations for the actual
  ordinal subsequences and their fixed key/slice functions.
- PendingStack/Push checks all three physical suffix arrays and saved parent
  bit cells; actual seven stores prepend the right task. SplitLocals selects
  the left child. RowsFrame/SplitRows preserve both exact child intervals;
  RowsLast derives the terminal ordinal load from interval contents/getLast.
- AgendaCost proves a logical price <= 1028*N matching all actual outer-case
  prices. FrontierBudget tracks cumulative completed leaves and active record
  mass, proving branches < N; BranchAddress supplies concrete nonzero/even/
  freshness facts under original allocation bounds. ReadFootprintStable proves
  that protected word agreement preserves the recursive read sets themselves.
- Successful closures construction-graph-checkpoint-v1 (679 targets) and
  address-read-stable-v1 (612), only permitted axioms. The physical invariant
  deriving parent separation, mapped cells, bounds and agenda/graph alignment
  remains open. Claim infinity; whole-guest/refinement/target/global K incomplete.
- OpenGraphSafety also checks that filling the first hole preserves safety
  of all remaining frontier writes, from explicit fresh-child/pending-read
  conditions and distinct frontier slots (frontier-safety-v1, 611 targets).

### 2026-10-17 — derive task ownership from the common backing layout

- BackingLayout gives actual six-pool addresses/extents, aligned/no-wrap bounds
  and pool separation. ImmutableRecords derives the exact original leaf slice
  cells and key views for each valid ordinal, with a protected-word frame.
- LayoutSeparation/Cells/WriteCells classify immutable reads and mutable zones,
  derive their disjointness and prove seven virtual allocation cells distinct.
  LayoutOwnership derives real scatter Ready from pools, immutable keys, valid
  ordinals and active rows. LayoutContext maps virtual allocation cells to the
  actual seven stores and derives all actual distinct/writable destinations.
- LayoutSplitMemory derives every store mapping and preserves all immutable
  key/record data through a complete split. LayoutDataPrefix protects the active
  primary prefix from allocation stores. LayoutLeftContext updates addresses,
  depth, destination, interval and ordinal validity; LayoutSplitInputs derives
  the actual split's parent premises. LayoutChildOwnership supplies the next
  left child's Ready using the actual updated rows and preserved immutable data.
- Successful layout-child-v1 closure (674 targets), only permitted axioms.
  LayoutLocated additionally classifies every concrete partial-graph read into
  immutable data or the installed header/branch arena (layout-located-v1, 667).
  Allocator/constructor entry, whole physical agenda/graph invariant and all
  original-map/whole-guest/compiled-target/global K obligations remain open.
- LayoutProtected/GraphFrame derive every installed-graph frame from geometry,
  protected reads and the active slot's frontier safety. LayoutGraphFill proves
  the complete actual split body installs its branch with the expected tree
  unchanged; no independent per-store/per-read premises remain in that result.
  LayoutLocationStep/FrontierSlots/BranchSafety/BranchFrontier preserve concrete
  graph locations, safe future frontier writes and distinct frontier addresses.
  Successful layout-checkpoint-v1 closure (690 targets), only permitted axioms.
  Continuing physical pending-read geometry, task interval preservation and
  full agenda induction; no finite certificate or target refinement yet.
- LayoutPendingReads classifies the real suffix/parent read addresses into
  lower pending-stack cells and installed parent-bit words, using the actual
  encoded depth predecessor (layout-pending-reads-v1, 673 targets).

### 2026-10-17 — actual split preserves the full construction invariant

- LayoutStackOffsets/Frame/Push derive all old physical stack-read separation
  from depth/parent geometry and prove the real right-task push preserves the
  suffix representation. PendingIntervals/Validity track increasing disjoint
  intervals, valid ordinals, nonempty saved tasks and legal saved bit positions.
- LayoutOtherInterval/PendingRows preserve all old sibling primary intervals
  and add the exact new right interval. LayoutLeafMemory/Graph/Frontier/Rows
  preserve immutable records, graph representation/location/safe/distinct
  frontier and all pending rows through the actual terminal tag store.
- LayoutTerminalCells/Body/Finish derive ordinal loads, all four pop reads,
  mapped destination and store separation for both actual terminal bodies.
  ResumeContext recovers exact saved-task addresses and all twelve live locals.
- FrontierAlignment connects current/pending ordinal tasks to concrete graph
  holes. OpenGraphSelect constructs the first-hole replacement from a nonempty
  frontier. AgendaBudget proves the three cases' cumulative allocation updates.
- ConstructionInvariant assembles graph, physical stack, intervals, immutable
  data, task metadata, locals and allocation budget. InvariantClock preserves
  it at any source clock. InvariantSplit proves a complete actual split body
  reaches a state satisfying the full invariant, with no assumed next-state
  invariant or independent per-store/read premises.
- Successful invariant-split-checkpoint-v1 closure (734 targets), only permitted
  axioms. Continuing unary/terminal full-invariant cases and whole-loop induction.
  Constructor initialization, original-map/whole-guest relation, target-clock
  composition and finite certificate remain open; claim stays infinity.
- Strengthened ConstructionInvariant with the original root-slot identity.
  InvariantUnary now proves the full invariant through the actual unary body.
  InvariantTerminal proves the actual leaf/pop continuation re-establishes every
  invariant component at the saved task, including exact resumed locals/metadata.
  InvariantFinish proves the actual final body returns and establishes the whole
  actual lookup representation at the original table root header cell.
- Successful invariant-root-checkpoint-v1 (735 targets) and invariant-finish-v1
  (727), only permitted axioms. All nonfinal body cases now preserve the full
  invariant, and the final case yields the intended represented tree. Continuing
  agenda-weight clock induction and constructor initialization; whole-guest,
  target transition bound and finite certificate remain open.

### 2026-10-17 — complete actual radix loop termination and clock bound

- AgendaWeightSteps proves exact record/bit-weight decreases and covers the
  actual terminal, unary and split prices. LoopCompose accounts for the actual
  surrounding while/fix_clock step and preserves all non-memory/non-clock/
  non-local control fields. LoopResult composes executions and clock bounds.
- LoopTermination proves the full actual main while loop terminates from the
  complete invariant, given 4*agendaWeight source clocks. It returns zero,
  establishes the exact expected actual lookup representation at the original
  table root, preserves control fields and consumes at most 4*agendaWeight.
  No successful whole-loop execution or next invariant is assumed.
- Successful loop-termination-v2 closure (741 targets), only permitted axioms.
  Initial 256-bit weight yields 1028*N after entry initialization. Source-clock
  facts are not target-transition bounds. Continuing initialization from real
  helper/header/array state and constructor hashes/allocations; whole-guest,
  compiler/target/global K and finite certificate remain open.

### 2026-10-17 — entire actual radix helper from initialized arrays

- InitialContext/InvariantInitial derive all real entered task locals and the
  whole loop invariant from mapped separated pools, immutable record/key data
  and a readable valid ordinal array of length N. HelperCore handles the actual
  nonempty test/return continuation. HelperExecution/Built compose all thirteen
  real prefix loads/declarations, whole loop and lexical restoration, including
  the empty case. The complete literal helper produces the expected root
  representation, preserves control fields and uses at most 1028*N source clocks.
- HelperEmpty separately needs only the actual empty ABI/header/root mapping.
  OrdinalArray proves the actual 0..N-1 array bounds, length and entry ordering.
- Successful ordinal-array-v1 closure (748 targets), only permitted axioms.
  Caller must still establish actual allocations and hashed array/record facts;
  original-map and whole-guest relation, compiled target/global bound and finite
  certificate remain open. Continuing constructor and fixed memcpy path.

### 2026-10-17 — fixed memcpy and actual constructor copy/store suffix

- Copy32 modules prove the entire fixed aligned, separated 32-byte memcpy,
  exact four word/32 byte values, actual ABI environment and ignored-result
  call restoring caller locals, at exactly two source clocks.
- ConstructorProgram/Stores/Copy extract the literal record loop and prove its
  entire after-hash suffix: actual copy call, record pointer and ordinal stores,
  index increment and exact final state. No successful copy oracle is assumed.
- Successful constructor-copy-v2 closure (615 targets), only permitted axioms.
  Actual Keccak behavior/frames, allocations and accumulated array invariant
  remain open; source clocks are not target transitions or a finite certificate.

### 2026-10-17 — constructor prefixes and actual final helper call/return

- ConstructorLayout/Memory/Frame classify the six actual suffix stores in
  separated pools, prove their exact values and preserve fixed header/records
  and earlier initialized hash/value/ordinal cells. Prefix/Data/Rows derive all
  helper immutable and exact ordinal-row premises at loop completion.
- ConstructorStep executes the real after-hash suffix from shared allocation
  layout and an earlier aligned scratch region, preserves fixed data/mappings,
  advances the full prefix and concrete locals, and pays exactly two clocks.
- CodeEnvironment/HelperEnvironment/HelperCall/ConstructorFinish prove actual
  argument/code lookup, helper callee setup, caller restoration and table return
  within 1028*N+1 source clocks, with the represented expected last-wins root.
- Successful constructor-step-v3 closure (774 targets), permitted axioms only.
  Actual hash calls, constructor loop assembly, htab_new/allocation setup,
  original-map/whole-guest relation, target/global K and certificate remain open.

### 2026-10-17 — actual persistent allocator and allocated layout

- PersistentAlloc proves the complete fixed successful allocator; Arithmetic
  derives guards, exact rounding, alignment and monotonicity from natural room.
  Environment/Call prove actual code/argument setup and lexical call behavior
  with updated heap_ptr, returned pointer and exactly one call clock.
- AllocationDomain derives mappings from the real challenge ordinaryDomain.
  AllocatedLayout derives full radix Valid/Mapped from exact htab_new offsets,
  including used-array padding, record/table ordering and heap-room facts.
- Successful allocated-layout-v1 closure (669 targets), permitted axioms only.
  Actual htab_new call/memzero/store composition and reachable heap-room facts
  remain open, as do hashing, original-map/whole-guest/target/global certificate.

### 2026-10-17 — complete aligned word-multiple memzero and real call

- ZeroProgram/Block/Conditions prove literal shapes, actual four-word and
  one-word blocks and guard/alignment tests. Both full loops execute with
  exact states and one clock per iteration. State/Tail/Execution compose the
  complete fixed function for aligned lengths divisible by eight.
- Memory proves exact nonlocal state/clock and memory outside-range frames.
  Environment/Call include actual code/argument lookup, callee setup, returned
  result and restored caller locals. Exact call price is n/32+(n%32)/8+1.
- Successful zero-call-v1 closure (624 targets), permitted axioms only. Initial
  table cap=4 byte-tail clearing still needs checking before htab_new can be
  fully composed; source clocks do not establish target/global certificate.

### 2026-10-17 — byte-tail clearing and literal table allocation sequence

- ZeroByteStore/LoopTail/ByteState/Small/SmallCall prove actual byte stores,
  full natural-index byte-tail execution, complete short aligned memzero and
  actual callee call/restore. Cap=4 costs exactly five call clocks and changes
  only its one aligned word. Arbitrary memory/be are retained in exact updates.
- ProgramPrefix composes actual declarations, guarded allocator calls and
  nonreturning commands with exact lexical restoration. TableNewProgram checks
  the full fixed htab_new action sequence. AllocationExpected connects natural
  expected cursor/alignment facts to actual allocation prefix steps.
- Successful allocation-expected-v1 closure (636 targets), permitted axioms.
  Concrete full htab_new sequence evidence remains to construct; no whole
  constructor/hash, original-map/guest/target/global finite certificate yet.

### 2026-10-17 — complete literal fixed htab_new

- ProgramPrefixAppend composes exact declarations/allocation/command execution
  while retaining lexical restoration. TableHeader/Initial/Locals/PreClear/
  Clear/Finish/Contexts assemble concrete evidence for all actual table steps.
- TableExecution proves the entire fixed htab_new for 32-byte keys, from actual
  source ABI/domain/code/heap-cursor and natural layout room/cap-shape facts.
  No successful whole constructor execution is assumed. Six actual allocation
  calls, nine header stores, both used-clearing cases, scopes/table return check.
- TableState exposes exact memory and nonlocal state/heap cursor. Source-clock
  cost is clearCost(cap)+6: 11 for cap=4, otherwise cap/32+(cap%32)/8+7.
- Successful table-state-v2 closure (699 targets), permitted axioms only.
  Header/record postconditions, caller setup and reachable heap-room facts still
  need connection; hashing/original-map/guest/target/global finite certificate
  remain open. Continuing concrete table postconditions and constructor setup.

### 2026-10-17 — actual table caller and constructor record-loop preparation

- TableCells/Memory prove distinct header stores and all four real helper
  pointer fields. TableRecords proves all earlier decoded record words survive
  every constructor write/clear and supplies Constructor.FixedData.
- TableEnvironment/Call prove actual htab_new argument/code/callee setup,
  complete lexical call, concrete memory/heap/clock result, binding/restoration.
  CallData transports concrete fixed header/record facts to that caller state.
- ConstructorArrayEntry/Prepare execute the real table call plus three actual
  pointer loads and zero ordinal declaration, exposing the remaining real
  record loop. Prepared data includes mapped arrays, fixed header/records,
  empty initialized prefix, all live locals and exact source-clock payment.
- Successful constructor-prepare-v2 closure (718 targets), permitted axioms.
  Layout/cap/heap-room and decoded-record premises remain to derive globally;
  capacity loop/hash calls, original map and whole guest/target/K remain open.

### 2026-10-17 — actual capacity declaration and whole doubling loop

- CapacityProgram proves literal guard/step and exact natural comparisons.
  CapacityLoop proves actual loop termination and state/clock/local frame.
  CapacityBound instantiates cap=4 with at most30 source clocks for N<2^31,
  sufficient cap in [2N+2,4N+4], cap<=2^32 and cap=4 or divisible by eight.
- CapacityEntry includes the actual initial scoped declaration and exposes
  the real htab_new caller continuation, retaining exact final cap/local frame.
  The count bound follows arithmetically from natural allocated record-array
  and heap-room facts; global reachability of those facts remains open.
- Successful capacity-entry-v1 closure (586 targets), permitted axioms only.
  Continuing fixed hashing/copy routines and constructor hash-loop assembly;
  original map, whole-guest/target/global K and finite certificate remain open.

2026-10-17: fixed Keccak permutation and byte-copy block checkpoint

- KeccakOracle/Ffi/Mapped/Call now prove the actual source-oracle reply,
  200-byte read from mapped state words, literal external/function execution,
  caller restoration, exact memory/FFI event update and one call clock.
- ByteArrayReads/Frame and ByteRegion prove mapped byte reads and writer/read
  transport frames; CopyByteProgram/Block execute actual generic byte copies.
- Successful closure: witness-radix-copy-byte-v3.log, 652 targets, only allowed
  axioms. Whole keccak256/constructor hash loop and global certificate remain
  open. Claim remains infinity; no full verification.

2026-10-17: complete generic fixed memcpy

- Actual aligned four-word/one-word and arbitrary byte-block/tail loops now
  execute from mapped reads/stores, with exact memory and source-clock cost.
- Whole function includes alignment selection, scopes/return and actual code,
  arguments, callee and caller restoration. Body cost <= length; call cost
  <= length+1. Complete frame outside destination byte/word footprint.
- Successful closure witness-radix-copy-general-call-v1.log, 640 targets,
  only permitted axioms. Used to close Keccak padding-copy execution gap;
  actual full hash, constructor loop and finite global certificate remain open.

2026-10-17: complete fixed Keccak block absorber

- Actual aligned and byte-expanded unaligned input expressions, all17 XOR
  lane stores and loop iterations, permutation call, scopes and return checked.
- Actual caller/callee environment and restoration check; cost18 body/19call
  source clocks, outside-state frame and nonlocal preservation except events.
- Successful closure witness-radix-keccak-absorb-call-v1.log, 678 targets,
  only permitted axioms. Full keccak256 block loop, padding/digest output,
  constructor and fixed finite certificate remain open.

2026-10-17: entire fixed keccak256 and actual caller

- All full blocks execute at20 source clocks each. Full padding tail includes
  clear/copy/both byte stores/final absorb/both output paths and remainder scope
  within194 source clocks. Complete initial clear, scopes and actual caller
  produce body<=202+20*floor(n/136), call<=203+20*floor(n/136).
- Preserves globals/code/oracle/host, caller locals and outside-buffer memory.
  No successful full hash or per-loop transition is assumed. Actual pointers,
  code/oracle and mapped-buffer premises still require allocation/input proofs.
- Successful closure witness-radix-keccak256-call-v1.log, 702 targets, allowed
  axioms only. Constructor hash loop, map refinement and global fixed certificate
  remain open. No finite claim or full verification.

2026-10-17: complete actual constructor array population and radix return

- AllocatedBytes/Keccak256Allocated derive all byte/word hash mapping from
  natural ordinary-arena extents/alignment. AllocatedAway and PoolFrame derive
  protection of every existing key/header/record/ordinal cell through hashes.
- Actual record arguments derive from decoded cells; real hash/copy/stores and
  increment establish next prefix. Whole actual record loop and radix helper
  return actual represented tree using observed hash digests. Bounds1374*N+1
  for max1024 nodes,10854*N+1 for max65536 code, in source clocks only.
- Closure witness-radix-constructor-populate-v3.log,874 targets, allowed axioms.
  Existing byte-frame lemmas were reused; an uncommitted duplicate module was
  removed. Allocator/capacity entry and global reachable premises, map/source
  refinement, compiler target bound and finite certificate remain open.

2026-10-17: entire literal candidate constructor and actual caller

- Capacity selection, actual htab_new and array preparation, complete real
  record hashing/copy/stores, whole radix helper, all scopes/table return and
  real caller/callee/code setup now compose to actual lookup representation.
- Exact heap-global update and caller locals restore; body bounds1378*N+47
  nodes(max1024),10858*N+47 code(max65536), call adds one source clock.
- Entry facts remain decoded records, actual code/globals/domain, ordinary
  allocated buffers before records and conservative heap-room inequality.
  Need reachable decoding/allocation proofs, original fixed-source map relation,
  whole-guest/gas/query/compiler/target bound and finite fixed certificate.
- Successful closure witness-radix-constructor-call-v1.log,915 targets, allowed
  axioms only. Incremental policy passes; claim infinity; no full verification.

2026-10-17: complete actual input_blob passing guard/allocation path

- WordCodec proves actual Guest/Pan little-endian codec bridges. SharedRead
  proves the real source oracle/call/load, including the actual appended event.
  HostLength/HostWords prove exact framed length and all eight data bytes,
  including final partial words and arbitrary mathematical list lengths.
- BlobProgram/LengthLoad/LengthGuard connect actual declarations/load/size
  guard. CopyStep/State/Loop/Walk/Domain/Return/Scopes compose every actual
  load/store/increment, all mappings from fixed domains/natural allocation,
  clock count, scopes and return. BlobExecute includes actual allocator call.
- Exact cost ceil(encoded_length/8)+1 <=16,777,215 source clocks. Exact heap
  update and unchanged host/oracle are checked. Preconditions still require
  actual code/domain/oracle, heap room and passing encoded-size guard.
- Successful input-blob-execute-v3.log,695 targets, allowed axioms only.
  Earlier errors fixed record layout, reserved scoped identifier, literal
  alignment logarithm, wrapper rewrites and alias arithmetic. No proof holes.
- Index now4177 modules/6630 printed facts (not progress percentages).
  Incremental policy passes61033 entries/2251449143 bytes, claim infinity.
  Copied heap bytes/SSZ/gas correspondence, failure paths, global potential,
  original-map refinement and target/finite certificate remain open.

2026-10-17: actual copied input bytes and scalar codec arithmetic

- CopyMemory proves every actual repeated store's exact copied word plus a
  complete untouched-cell frame. ByteDecode proves packed-word byte selection;
  CopyBytes supplies actual little-endian heap byte reads from the copied words.
- BlobExecute now exposes exact resulting memory, ordinary domain and endian.
  BlobBytes.execute_bytes composes whole actual input_blob with exact HeapInput
  over the encoded extent and <=16,777,215 source clocks. No mathematical
  input-list length bound. Successful input-blob-bytes-v1.log,1024 targets,
  only permitted axioms; includes all changed dependency checks.
- For lists of length >=2^64, bytes after the encoded length may still be
  nonzero original input bytes. HeapInput intentionally claims only the encoded
  extent; no false zero-tail or full decoder-mirror equivalence is assumed.
  Fresh unfilled heap cells need a reachable zero-memory invariant.
- WordAssemble proves actual 4/8-byte bitwise assembly equals natural LE sums
  (input-word-assemble-v4.log,606 targets). Explicit multiplication proofs avoid
  omega recursion-depth blowup from accumulated redundant inequalities.
- Index4182 modules/6641 facts; incremental policy passes61038 entries and
  2251465241 bytes, infinity. Work continues on actual SSZ scalar reads/guards,
  source-map refinement and global/compiler/target finite certificate.

2026-10-17: fixed payload gas expression and real SSZ offset-validator paths

- ScalarProgram/Scalar64 check exact expanded 4/8-byte reads, shifts and ORs.
  HeapScalar connects copied heap bytes to the challenge's minimal gas reader.
  FlatAddress/ScalarCongr/FlatScalar check flattened additions rather than
  assuming syntactic equality of the generated and nested address expressions.
- PayloadGas extracts exact gas store15 from fixed decode_payload, proves its
  literal shape and actual expression bound200M from explicit copied extent,
  payload position and container offset facts. Those reachability premises
  remain unproved. Closure input-payload-gas-v3.log,1032 targets, allowed axioms.
- SszFail proves whole real raise/body/callee/call with actual SszErr shape and
  one call clock. OffsetsProgram checks whole-body shape and final equality
  guard's exact success/mismatch executions. StepProgram/Checks check actual
  current/prior reads, range/order/signed-index expressions. ValidStep/Loop/
  Walk/ValidExecute compose complete actual nonempty valid validator, cost=count
  source clocks and exact frame. Fixed count<=8 includes all five real callers.
- FaultChecks/FaultStep prove both actual range/order rejection paths, real
  SszErr10/11, no resumed increment and exact one call clock/lexical restoration.
  Unrestricted loop, whole normal-return inversion and actual decoder container
  positions/offset stores still remain. No whole decoder or global claim.
- Joint successful input-offsets-fault-step-v2.log,1042 targets, allowed axioms.
  Indexed4199 modules/6691 facts, not percentages. Claim infinity, no verifier.
- Proof traps: raw BitVec.or produced by unfolding OrOp.or does not match the
  notation-keyed or_zero/or_assoc simp rules; explicit raw-key wrappers fixed
  misleading whnf timeouts. Fin numeral projections needed local rfl facts.
  Ite reads evalHOLExact while while reads evalHOLFinite; preserve the wrapper
  expected by the outer evaluator. BitVec.add_sub_cancel is the actual name.
  Unannotated congrArg intermediate avoids expected-state equality forcing.

2026-10-17: unrestricted whole SSZ offset validator and actual caller

- OffsetsUnroll retains the real while clock clamp and every abnormal result.
  AnyLoop covers arbitrary mapped words, normal completion or actual SszErr10/11
  within rounds+1 clocks. AnyExecute adds final equality guard/all scopes;
  nonempty count<=8 costs<=count+1. Normal proves first=fixed without assuming
  ranges/order/first equality. No schema-validity premise is introduced.
- Environment supplies all four actual argument bindings. Call includes actual
  lookup/callee/body/return/exception behavior and restores caller locals.
  CallNormal proves any genuine normal ignored-result call yields first=fixed
  and post={source with clock:=source.clock-paid}, paid<=count+2.
- HeapFrame transports copied-input bytes across matching fields and real word
  stores outside the natural copied extent; mapping is independent of contents.
- Successful joint input-heap-frame-v1.log,1116 targets, only permitted axioms.
  Indexed4207 modules/6701 facts (not percentages). Caller proofs still require
  actual four evaluated argument values, code/exception-shape and mapped words.
- NEXT: fixed decode_stateless_input copies LD_LE32(p) and LD_LE32(p+4) to
  ssz_offs after p+=2,len-=2. Normal count2/fixed16 call must yield le32(input,2)
  =16. Then np=p+o_npr=blob+18; nlen>=44 guard and three stores precede normal
  count3/fixed44 call, yielding le32(input,18)=44. np+o_pl=blob+62, then
  decode_payload length>=540 ensures gas byte474 is within copied extent.
  Connect actual stores/guards/allocations and their byte frames, not only the
  high-level InputDecode mirror. Generic HeapInput and scalar/frame results
  are ready; no decoder-prefix composition module is written yet.
- For failed AnyExecute frame attempts, updating both sides of the full frame
  with one uniform clock normalized an alias too early. Rewrite the existing
  emptyLocals finished frame first, then finished.clock and Nat.sub_sub. For
  CallNormal, keep target.locals in the reconstructed full equality until eta
  reduces the left record; rewrite caller locals afterward.
- Fixed certificate/global/gas/query/target/ROM/map relation still open; claim
  infinity and no full verification. RAM1.3GiB/disk58% at this checkpoint.

2026-10-17: first actual decoder offset stores/guard, retained range facts

- Strengthened AnyLoop/AnyExecute/Normal/Call/CallNormal to retain every offset's
  lower/upper/nondecreasing facts on normal completion, not just first=fixed.
  These facts are required to justify the real subsequent slice extents.
- StoreScalar proves actual flattened uint32 read+word store and HeapInput
  preservation using natural separation. HeaderProgram extracts the exact fixed
  decode_stateless_input tail after the first five header commands. HeaderPair
  executes both literal stores, proves exact words and unchanged copied bytes;
  actual mapping follows from aligned allocated ssz_offs before the input.
- HeaderGuard.guard_normal inverts the actual two-store/count2/fixed16 prefix:
  le32(input,2)=16 and16<=le32(input,6)<=total. Post is exact pairState except
  <=4 source clocks; HeapInput survives. No successful scalar/guard is assumed.
  It does explicitly assume actual normal prefix execution, shifted p=blob+2,
  >=10 encoded bytes, globals/code/exception shape and natural allocation room.
- Successful input-header-ranges-v2.log,1120 targets, allowed axioms only.
  Indexed4211 modules/6705 facts, claim infinity; no full verification.
- NEXT concrete choices: source entry is len<2 fail1, schema-byte mismatch fail2,
  p+=2,len-=2,len<16 fail80, then Header.afterHeader. On passing entry derive
  encodedlen>=18 and exact shifted locals; all three rejection paths need real
  SszFail exception/cost. Then first guard normal + its upper/order facts imply
  np=blob+18 and safe nlen=wit-16. nlen>=44 gives encodedlen>=62. The second
  prefix has three real o_pl/o_vh/o_rq declarations from offsets18/22/58,
  three writes to ssz_offs[0/8/16], count3/fixed44 call and scoped continuation.
  Its normal return must yield le32(input,18)=44, so payload ptr=blob+62;
  payload len>=540 then places gas read474 safely inside copied input.
- All source-map/compiler/ROM/global budget/query/finite certificate obligations
  remain. No production pnk change, so no repeated native/EEST run was needed.

2026-10-17: complete actual decoder entry and first-container normal-return inversion

- EntryProgram extracts exact first five header commands. Schema proves both
  actual byte loads/comparisons/OR. Guards include real SszFail call/exception.
  Entry handles every initial short/schema/container-length rejection at one
  call clock and exposes shifted afterHeader on passing checks. EntryNormal
  inverts an actual normal decode return into encodedlen>=18 and schema21,1.
- Ready derives actual guard ABI/mapped cells; AfterNormal rules out actual
  range/order/final-equality exceptions before continuation. FirstContainer
  composes whole fixed decoder normal return into schema, first offset16,
  16<=witness offset<=encodedlen-2, exact next continuation and preserved input
  bytes. No valid schema or fixed first offset is assumed.
- Preconditions still initial HeapInput/argument locals/code/exception shape,
  natural aligned allocated ssz_offs before input, heap extent and clock>=4.
  Schema and first two container offset values now derive from execution.
- Successful input-first-container-v1.log,1128 targets, allowed axioms only.
  Indexed4219 modules/6718 facts, not percentages; infinity/no full verification.
- NEXT: Header.continuation is actual dec o_npr/load ssz_offs, dec o_wit/load+8,
  decCall si=alloc96, store si+88 LD_LE64(p+8), dec np=p+o_npr, dec nlen=o_wit-
  o_npr, nlen<44 fail81, then second request declarations/stores/count3 guard.
  FirstContainer gives o_npr16 and witness range; derive np=blob+18, natural
  nlen=wit-16. Passing nlen>=44 implies encodedlen>=62. StoreScalar64 can reuse
  flat64/heap_le64 for real chain-id read at input10..17; heap allocation and
  separate destination preserve HeapInput. No request-prefix module exists yet.
- Bool.not_eq_true is the propositional-negation form; Bool.not_eq_true' is
  required for (!b)=true. Explicit ne_eq exposes byte-word equality iff under
  Ne, and rfl finishes OfNat versus # literal forms after simp only. Preserve
  scalar read facts with explicit change before default simp rewrites byte
  ofNat/toNat into setWidth.
- Entry shift_execute also exposes both actual individual assignments for
  nested continuation composition; no sequence-associativity assumption.
- Production remains unchanged; global/original-map/compiler/ROM/target/K
  obligations remain. All work local/offline; account status is monitored
  separately in temporary files, not in committed proof artifacts.

2026-10-17: complete actual request prefix from full decoder normal return

- StoreScalar64 proves actual flattened uint64/store/input frame. RequestProgram
  extracts both real prefix and three-declaration/three-store/count3/fixed44
  request tail. PrefixProgram uses actual ProgramPrefix actions and all five
  lexical restorations; Load checks real o_npr/o_wit reads. Chain checks actual
  allocated SI+88 chain-id store from blob10..17, with natural mapping/frame.
- Positions proves real np=blob+18, nlen=witness-16. Setup composes both loads,
  actual alloc96, chain store and declarations as Executes evidence. PrefixEntry
  includes real SszErr81 length rejection; passing prefix costs one allocation
  clock, rejecting length adds one. PrefixNormal derives encodedlen>=62 and
  safe request length>=44 and<=encodedlen-18 from actual normal prefix return.
- FromHeader composes Header.first_container and all prefix evidence from a
  genuine normal fixed-decoder return, exposing actual requestBody/inner post
  and copied HeapInput. ReadyFrame retains code, exceptions, structs, domains,
  endian, full FFI, globals updated only heap_ptr=rounded(cursor,96), and clock
  >=source.clock-5. Initial source clock>=6; use>=10 when next guard needs5.
- Entry still requires runtime code/shape/domain, original HeapInput/arguments,
  aligned natural ssz_offs64 before input, cursor after copied extent, alloc96
  room and aligned cursor. No schema/first fixed offset/request length assumed.
  Source-normal allocation-room inversion and reachable startup facts remain.
- Joint successful input-request-from-header-v2.log,1140 targets, allowed axioms.
  Indexed4229 modules/6735 facts (not percentages), infinity/no full verifier.
- NEXT: requestBody is exact dec o_pl=flat32(np,[]), dec o_vh=flat32(np,[4]),
  dec o_rq=flat32(np,[40]), three stores of locals to ssz_offs0/8/16, actual
  count3/fixed44 call, then Request.continuation (decode_payload etc). Raw scalar
  offsets18/22/58 lie in proven encoded extent62. Need all declarations/scopes,
  exact three stored words/input frame and normal guard inversion to raw first
  offset44, monotone remaining offsets and request bounds; then payload ptr62.
- Generic word_read at an opaque state fixed an implicit-transparency failure:
  unfolding bound-state records inside simp left a mismatched DecidablePred
  argument. Prove read for abstract state first, then apply to the bound state.
  Explicit restorePrefix avoids an unsynthesized existential function witness
  before constructing the ProgramPrefix Executes proof.
- Production pnk unchanged; no repeated native/EEST tests. All global original-
  map/compiler/ROM/target/query/potential/K obligations remain open.


Request guard and payload-callee entry continuation (2026-10-17):
- All three actual request scalar declarations/stores check, with exact array
  words, lexical scopes and preserved copied HeapInput. Count3/fixed44 validator
  covers normal and SszErr paths; normal whole request return derives raw44,
  range/order and actual payload pointer blob+62, contained payload slice.
- Real payload >=540 guard, SszErr50 caller propagation, ABI and normal-callee
  inversion check. Full normal fixed decoder composition derives extent>=602,
  raw first offsets16/44 and actual callee entry with HeapInput/code/domain/
  globals heap_ptr=rounded(cursor,96), clock >=original-11. Original clock>=12.
- RequestGasFromHeader derives actual gas expression <=200M there; it does not
  yet prove the later payload-field store. Initial runtime facts, copied memory,
  natural ssz_offs64 and alloc96 geometry remain explicit.
- Successful joint input-payload-flat-prefix-v1.log,1153 targets, permitted
  axioms only; prefixProgram extracts actual alloc136/header stores/four scalar
  declarations. HeapFlatScalar supplies reusable flattened copied-field reads.
- NEXT: actual payload allocation136, two header stores and four declarations
  from this callee entry. Raw offsets498/566/570/590 fit proven extent602. Execute
  four stores/count4 fixed540 guard, extra-data length<=32 guard; whole real
  ssz_split_var_list and ssz_fixed_list_count calls/input frame before gas store.
  Then reach gas store and preserve the <=200M payload-field invariant. Actual
  request/witness records and startup/global reachability remain afterwards.
- Opacity matters: helpers over abstract states for command_single/prepend and
  state_from_frame avoid eager evaluator reduction when applying constructors
  to deeply updated states. HeapInput transport should project memory/domain/
  endian from nonlocal frame instead of unifying it against record-update eta.
- Account read-only watcher still active;17% and zero reset credits. Original
  earned reset used successfully earlier; no additional reset can be requested.
- No finite claim/full verifier, production artifact unchanged.

- Indexed4242 modules/6763 printed facts (not percentages); incremental policy
  passed61098 package entries. No full verifier.


Payload allocated prefix checkpoint (2026-10-17):
- HeaderStores, OffsetDeclarations, PrefixSetup: actual alloc136, pointer/length
  header writes, four actual reads input498/566/570/590, scopes and HeapInput.
- OffsetsProgram/Stores/Normal: four actual ssz_offs writes and all actual count4
  validator normal/fault paths, normal raw498=540 +range/order, <=6 call clocks.
- PrefixGuard/ExtraGuard/PrefixExtra: actual normal afterGuard execution entails
  all prefix facts, raw566-540<=32 and actual afterExtra continuation. At most7
  source clocks including allocation. PrefixExtra clock assumption>=8 covers
  actual SszErr51 rejection. Still requires alloc136 room/current natural cursor,
  runtime code/domain/copied HeapInput, initialpl arguments and extent>=602.
- Successful joint input-payload-prefix-extra-v3.log,1163 targets, only allowed
  axioms. No production byte changes, finite K or full verifier. Account17%,
  zero reset credits; read-only watcher active.
- NEXT actual afterExtra begins storepl16=p+o_extra, storepl24=o_txs-o_extra,
  scoped ssz_split_var_list(np+o_txs,o_wd-o_txs,2^63-1), two result-field stores,
  scoped ssz_fixed_list_count(o_bal-o_wd,44,2^63-1), then gas-field header stores.
  Need whole nested callees/read-only input frames, their natural heap room and
  record/length bounds before reaching gasstore. Split_var_list actual body at
  Guest/Ast.lean5696; fixed_list_count5745; udivmod691 (64-iteration long division).
  No existing Solver udivmod summaries found. Var-list uses shift2, not udivmod.
- FUPDATE key comparison is updated-key==query, opposite of intuitive queryfirst.
  simp-only does not reduce false=true conditional unless explicit reduction.
  `change` expected prepared/declaredState alias before rewriting scalar equality
  avoids a simp implicit-transparency mismatch; field projections after rw can
  require explicit rfl. Bind_lookup_other takes MlS binder!=query, not Stringne.


Variable-list entry checkpoint (2026-10-17):
- RawScalar: raw byte/uint32/uint64 bounds and ofNat-toNat at every input index;
  no host-window/size premise. Use these instead of HostGas.le32_eq for dynamic
  starts. VarList.Program extracts all actual entry/first/count/allocation/loop/
  finalstore/return AST shapes (Pan ExpHOL uses .rstruct/.panop; ValueHOL.rStruct).
- Entry: real empty pair return0 clocks, short SszErr20 costs1, passing real
  copied uint32 first declaration with exact local scope. Slice containment only.
- FirstChecks: actual first zero/alignment/range composite predicate, shift2
  count, nonempty positive count with4*count=first<=length. CountChecks actual
  limit condition andpanop count*16. FirstGuards all real SszErr21/22 branches
  and exact allocator continuation, lexical count restoration; no alloc yet.
- NormalEntry: actual whole-function normal return yields empty pair or length
  >=4, positivecount=rawfirst/4,4count=rawfirst<=length,count<=limit, actual
  allocation-call normal continuation. No normal-offset validity assumed.
- Successful input-varlist-normal-entry-v1.log1160 targets; allowed axioms only.
  Next whole alloc16count and record loop/finalstore/return, copied input frame,
  ABI/caller; nonempty/allfault branches. Then actual fixed_list_count/udivmod
  and payload gasstore. Nothing finite/global/target verified.
- Dynamic loop LD_LE32 addresses use flattened add[p,panop(i*4),byte], so static
  flat32(base,[constants]) does not match. Next useful helper: generic add-args
  flattened uint32 congruence or direct actual dynamic byte-address evaluation.
  Reuse Scalar.op_congr/byte_congr/shift_congr and HeapFlatScalar/HeapScalar;
  keep actual AST rather than replacing dynamic subexpressions syntactically.
- AND fold starts allones. A local universally quantified foldedAnd lemma
  avoids simp key mismatch AndOp.and vs notation and survives first=0 rewrite.
  badFirst is Prop: define its Decidable instance explicitly for theorem ifs.
  Prefer plain simp with split conditions over simp_all to avoid recursive simp.


Variable-list actual record-body checkpoint (2026-10-17):
- PairedScalar dynamic flattened addresses/read32 supports actual p+i*4+byte AST.
  StepProgram actual closed loop/finalstore shapes; OffsetRead six real expression
  reads. Layout.Plan inputptr/array/start/length/count, positivecount,4count<=len,
  contained encoded slice, sourceBase/inputalign/arrayalign/fresh-after-input+
  allocroom16count. It is explicit entry geometry, not reachable startup facts.
- Layout provescount<2^31, dynamic read extent, exact row/length-cell natural
  addresses, ordinary mapping and every record store preserves copied input.
- Checks actual three-way offset check and signed loop/hasPrevious tests. The
  literal9223372036854775808 sign hypotheses are needed for simp matching2^63.
- StepStores whole optional prior-length store/current pointer store/localprev+i
  updates. ValidStep/ValidBody actual entire accepted record body incl scalar
  scope even atclock0; FaultBody actual rejection SszErr23 before any store,
  exact scope and1callclock, HeapInput/nonlocal frame. Unroll activewhile retains
  actualclockclamp+allresults. Walk exact model with iteration_clock/control/i/
  prev/otherlocals andwalk clock/control/otherlocal frames.
- ScalarScope declare_execute +HeapInput.bind/restore andScopeLookup restore_other
  factor opaque-state proofs. This fixed a kernel20k timeout in ValidBody (25s)
  without raising heartbeat/resource limits; newValidBody checked2.4s. Avoid
  reconstructing whole scoped byte-frame proofs inline over large symbolicstate.
- Successful joint input-varlist-walk-v1.log1283 targets, only allowed axioms.
  Account18%,0resetcredits, watcheractive. Fullfiniteclaim remainsinfinity.
- NEXT AnyLoop: actual loop alloffsets normal orSszErr23, cost<=rounds+1, exact
  normalwalk and every ValidAt/HeapInput/control frame. Normalstatecost=rounds.
  UsePlan.count_small forsign. Add previousIndex:0<index -> previous=currentWord
  input plan.start(index-1); useOffsets.ValidAt first total (currentWord input
  plan.start) index. Valid_body/fault_body run atdecClocksource. NormalIHnext
  iteration_index/previous/other/control preserve allformals. Faultpaid2 incl
  activewhileclock; normalnextpaid=ihpaid+1. Fault memory may retain prior record
  writes, so useBackingLayout.control (stripslocals/memory/clock) +HeapInput,
  not emptyLocals=initial-onlyclock over wholeloop.
- Next recordcell memory representation, final length store/return, actualalloc
  andcaller ABI; then fixed_list_count/udivmod and actual payload gasstore/global.
- New struct fields require each name on its own line (`start length count :Nat`
  instead declares a function field). Multiline record memory RHS needsparens.
- Unroll loop_test_read returnsQueryBranch.eval whilewhile_total uses evalHOLFinite:
  add typed finiteTest:=test before rw. Faultbody useguarded.trans(if_posbad) to
  produce typed rejection; simp noProgress can occur at a folded local alias.


Whole variable-list loop/tail checkpoint (2026-10-17):
- AnyLoop actual arbitrary offsets: none with exactwalk +allOffsets.ValidAt and
  paid=count, oractualSszErr23; <=count+1,exactclock/control/HeapInput. Lastloop
  proofneeds previousIndex:positiveindex=>prev=currentWord(index-1). Baseindex0
  vacuous; nextprev=curindex. IHfirst/total arefixedcontext, notexplicitargs.
- Cells row/length injectivity/separation; IterationMemory exact two memory
  effects. Filled prefix and walk induction initialize pointers/all butlastlen.
  WalkPrevious gets lastprev; Return realfinalstore/actualrStructreturn with
  noextra clocks; Complete allpointer/lencells. LoopReturn coversall actual
  loop+finalstore/return outcomes andcomplete validrecords. AllocatedTail wraps
  real i=0/prev=first scopes andretains restoration; noallocator call yet.
- Successful joint input-varlist-allocated-tail-v1.log1292targets allowedaxioms;
  claiminfinity, nofullverifier. Account19%,0resetcredits, watcheractive.
- NEXT strengthen all-outcome memoryframe outside fresharray extent, in addition
  toHeapInput. Current summaries preserveinput/control/complete records but do
  notyet expose general oldheap preservation, needed for earlierpayloadheaders.
  Add ArrayFrame overqueryNat<arrayNat orarrayNat+16count<=queryNat. Prove each
  modeliteration/walk/failure/finalstore frame via naturalcelladdresses. Extend
  AnyLoop/Return/LoopReturn/AllocatedTail outputs before composingactualalloc.
- Allocator composition next: actualcount*16 expression/read +args, real
  PersistentAlloc.call_execute, sourceheap_ptr=plan.array, Plan.arrayRoom. Entry
  =bind(post{sourceclock-1}array(ofNat16count))arrarray. Get allocated_execute
  there, return heapglobal rounded(array,16count), exactcallerarrscope; normal
  costs count+1, fault<=count+2 bodyclocks. Preserveinput +outsidearrayheapframe.
  Then FirstGuards/Entry/allrealssz_split_var_list ABI/caller. OOM/trap path and
  globallyreachable allocationroom stillopen. Afterwards fixed_list_count/
  udivmod and actualpayloadgasstore/global/target finitecertificate.
- simp only can leaveifTrue/ifFalse after rewriting a premise (seeIterationMemory
  andComplete); include explicit ↓reduceIte. RecordmemoryFrame usecontrol strips
  locals/memory/clock; failedloop mayretain earlierarraywrites. Complete has
  wordlengthdifferences; allValidAt will justify natural-length interpretation.


Variable-list whole normal caller checkpoint (2026-10-17):
- MemoryFrame fresharray extentOutside word-frame incl allrealrecordloop outcomes,
  finalstore/return/scopes; strengthenedAnyLoop/Return/LoopReturn/AllocatedTail.
- Allocation actualpanopcount*16 +PersistentAlloc.call_execute +arrscope +whole
  initializedtail. Globalsadvanceexact, input/oldheapoutsidearraypreserve; normal
  count+1 /fault<=count+2 bodyclocks. Plan freshgeometry/runtime/roomexplicit.
- NormalEntry nowretains exactfullpost first/count scope-restoration equality.
  EncodedCount realshift2=rawfirst/4 andcount<2^30. BodyNormal derivespositivePlan
  fromgenuine nonempty normalwholebodyreturn;completecells/validranges/exactclock/
  globalupdate/copyandoldheapframes. NormalSummary includesactualemptycase and
  conservativearrayNat+4*lengthroom, normalbodycost0orrawcount+1<=length/4+1.
- Environment actual3argABI/returnShapecomb[one,one]. CallNormal.callee_return
  genericdecCall normalinversion andCallResume.return_execute installarbitrary
  tuplevalue/restorecallername. CallerNormal genuinevariablelistcall normalreturn
  exposesactualcontinuation, callerlocals.update(name,tuple), HeapInput/oldwords
  beforearraybase, control sourceorheapupdate, exactcallerclock1+bodycost, lower
  sourceclock-(length/4+2). Sourceclock>=length/4+3 neededbycomponentproofs.
- Successful joint input-varlist-caller-normal-v2.log1301targets, allowedaxioms.
  Account19%,0resetcredits watcheractive; nofiniteK/fullverifier.
- NEXT PayloadTransactionsProgram afterExtra exacttwo storespl16=p+o_extra and
  pl24=o_txs-o_extra; scopedtxs callssz_split_var_list(p+o_txs,o_wd-o_txs,2^63-1).
  ApplyCallerNormal preservingactualp/pl/len/offsets andcopiedinput, thenreal
  pl32=rfield0txs,pl40=rfield1txs,scopednwd callssz_fixed_list_count(o_bal-o_wd,
  44,2^63-1). Need actualudivmod64-loop body+fixed_list_count/caller proof next.
  Afterward allremainingpayloadstores nofurthercalls: pl48withdrawalptr,56nwd,
  64balancesptr,72balancebytes,80blocknum(raw404+62),88gas(raw412+62=474),96gasused,
  104timestamp,112blobgas,120excessblobgas,128slot. Max532+62+8=602 alreadyderived.
  Proveactualgasstore<=200M andlaterdistinctstores preservefield88 beforeactual
  return; thenwholepayloadcaller/RootSI/header/witnessdecoder/nodedbglobal entry.
- Important zero-case: realvarlist emptyreturns(pointer0,count0). Auditconstructor
  entrypremises forN0: anyunconditionalpositive/mapped recordsbase couldexclude
  this realcase; relaxunderpositivecount orproveemptyconstructorpathseparately.
- Parenthesize booleanAND before equality: `(a && b)=true`; bare`a && b=true`
  elaboratesa&&decide(b=true) coercion. ShapeOf/shapeEq wellfoundeddefs maynotrfl;
  use shapeEqHOL_eq_true+shapeOfHOLExact equations for actualtupleShapecomb2.
- Rewriting count_encode atbind_lookup_same changes bothStatebinder andRHSword,
  breakingtheoldreadytype. InsteadtranslookupSame withcongrArg(some.val.word)
  count_encode tochangeonlytheRHS. Genericcallee_return generalize rewritesits
  fixed-calleegoal too; returnedbranchusesrfl, notoldoutputEq.

Payload transaction/withdrawal checkpoint (2026-10-17):
- PayloadTransactionsProgram/WordStore/ExtraStores/TransactionsNormal derive real
  tx slice containment from4offset validator, executepl16/24 extra stores, then
  actual VarList caller and normal continuation; empty tx list included.
- UDivMod Program/Step/Frame/Loop/Setup/Built/Call actual zero-divisor guard skip
  for nonzero divisor, early return or64 rounds including dynamic shifts, signed
  loop tests, assignments/conditional subtraction/q updates, lexical restoration,
  tuple ABI. Body0or64, call<=65 sourceclocks; full memory/control frame. Does not
  prove quotient/remainder arithmetic correctness; no such hypothesis assumed.
- GuardNormal generic real ssz_fail nonresumption. FixedList Program/Tail/Normal/
  Environment/CallerNormal actual division call, error30 remainder guard/error31
  limit guard/word return/ABI/resumption, body<=65,call<=66; normal count<=limit.
- PayloadTransactionStores/WithdrawalsNormal actualpl32/40 tuple stores and nwd
  call44 divisor, copied bytes preserve, localsrestore/clock/control frame,
  afterWithdrawals actual normal continuation. Joint successful
  input-payload-withdrawals-normal-v1.log1329 targets, all permitted axioms.
- State-control simplification may allocate>11GiB. Replaced whole-state
  simplification with abstract field_control/allocated_field_control equalities;
  runtime unchanged. Qualified QueryBranch.bind avoids Bind.bind simp ambiguity.
- evalHOLFinite DecidablePred instances can differ computationally from explicit
  classical QueryBranch.eval; UDivMod.finite_eval proves equality via Subsingleton
  rather than assuming definitional equality. General fmap update uses BEq in
  fixednormal lookup; explicitly prove literal BEq=false and simplify Bool.
- NEXT afterWithdrawals11stores+return, actualgasstorepl88 raw474<=200M, preserve
  laterfields. Need fullallocated payload caller/scopes; then fullSSZ/witness/root
  global entry, constructor emptyrecord case, global Q/budget/source-map/target K.
  Claim infinity. No fullverifier. Account20%,0resetcredits watcheractive.

Whole actual payload normal body checkpoint (2026-10-17):
- PayloadFields generic real field-store sequence/finalreturn, copiedinput/clock
  frame and actual cellValue reading. Memory-only fieldMemory accumulator avoids
  nested whole-state update duplication (prior assembly200kheartbeat timeout).
- RemainingProgram exact eleven actual stores after withdrawalcounter, includes
  flat64 offsets404,412,420,428,512,520,532; finalgasfield88 exactrawinput474.
  RemainingReads ties allseven to copiedinput; RemainingExecute wholeactualsuffix
 0clocks, realreturnpl,HeapInput and finalgasfield. StoredGas bound from fixed16/44
  toactualdeclaredGasLimit<=200M.
- TailNormal afteractual txscall continuation allstores+withdrawalcounter+suffix;
  AfterExtraNormal composes realVarList, includesemptyrecords/pointer0, intoalltail.
  AllocationControl extracts domain/code/shapes without expanding conditional
  whole-state record; avoids>8GiB simp allocation.
- Strengthened PayloadPrefixNormal/Guard/Extra exact post=restoreStack/Prefix
  equality retained. PreparedFacts reallivep/pl/len/heapglobals and actual136
  roundedcursor geometry. AllocatedNormal completeactualafterGuard, BodyNormal
  includesminimum540error50guard, derivesextent602 fromcontainedslice.
- BodyNormal prems: heap_ptrcursor,ordinarydomain,inputalignment/lower,
  cursorAfterinput, cursorNat+136+4encodedExtent<=heapend, staticssz_offsbefore
  input, runtimealloc/offsets/fail/udivmod/varlist/fixedlist, clock>=extent/4+76.
  Onactualnormalreturn value=wordcursor, memorycursor88=rawword474, HeapInput,
  postclock in[sourceclock-(extent/4+75),sourceclock]. No listvalidity premise.
- Successful input-payload-body-normal-v1.log1340targets, allowedaxioms only.
  NEXT RequestStoredGasFromHeader derive realpayloadcursor from SI96alloc,
  roomstrongcursor+232+4extent, enoughouterclockextent/4+87; actualpayloadpost
  field88 bound200M fromwholeHeader.body normalrun. Then payloadcaller exact
  resumption/rootSI/witnessdecodedrecords and global Q/heap/gas/target refinement.
  No finiteK/fullverifier. Account20%,0resetcredits read-onlywatchactive.

Outer actual gas-store/caller checkpoint (2026-10-17):
- RequestStoredGasFromHeader complete Header.body normalrun =>actual allocated
  payload afterGuard return, realgasfield88<=200M, copiedinputpreserve. Derives
  actualpayloadcursor rounded(oldcursor96),room232+4encodedExtent, enoughouter
  extent/4+87. Keepsactualentry andpayloadPostrun. Success1341targets.
- EvaluationFields imports existing HOL-tagged PanProps.evaluate_invariants,
  exact codec transport =>everyevaloutcome preservesdomain/endian/code/shapes.
  PayloadCallerNormal actualfullbodycalleecall/resumption, returnswordcursor,
  tuple/ABIshapechecks,savedcallerlocals/gasfield/HeapInput, <=extent/4+76 clocks.
  Success1351targets. Indexed4322modules6930facts, allowedaxioms only.
- IMPORTANT constructor0 audit confirmed ConstructorExecution.execute unconditionally
  requiresrecordsLower>=2701131776 and scratchBefore records. Actualemptyvarlist
  returns recordsbase0/count0. Need separate count0 actualconstructor path; no
  count0 records access/hash necessary. Plan use capacity_entry count0, forcecap4
  (2<=cap<=4 andshape), fake logical records=table for layoutReady, prepare_execute
  doesn'trequireactualslice_arrbinding; skiprealrecordloop directlyi0/n0, finish
  withvacuousFixedData/prefix0. No hashEnvironment/scratch/recordpointer premises
  ontheemptycase. Entiretableallocation/helper/return/scopes retained.
- Next then VarList record-array info exposedfromnormalSummary/caller (currently
  Complete/validAt discardedafterBodyNormal). Needed decode_bytes_list actual
  maxb70guardreadonlyloop andconstructorrecords/lengthcaps1024nodes65536code.
  Keepactualemptycase inallinterfaces. No finiteK/fullverifier. Usage21%,0credits.

Empty constructor and whole bytes-list caller checkpoint (2026-10-17):
- ConstructorEmpty.execute_empty: anyactualslice_arrvalue permittedincluding0;
  n0 forcescap4; actualallocation/clearing/prefix, loopskip, actualhelper/return,
  allscopes. Logicalrecords=table usedonlyaszero-extent layout, neverread. No
  hashEnvironment/recordmapped/scratch premises. Actualheap table+304, <=43body
  sourceclocks (conservativecap<=30); require47entryclock.
- ConstructorEmptyCall actualdecCall arbitraryrecordsNat includes0, tupleABI,
  scalarreturnedtable binding, emptyrepresentedtree, heapadvance, callerrestore,
  <=44sourceclocks; require48. Successfulconstructor-empty-call-v1.log1275targets.
- VarList.Records normalwholebody givesPlan/Complete/validAt oractualemptycase.
  CallerNormal strengthenedtoexposethat concretearrayandcheckeddecodedcount<=lim.
  RecordCells decodedCount empty0/decodedArray empty0, actualmappedlencells and
  recordLength adjacentwordoffsetdifferences, count<=slicelen/4 and<2^31.
  CountLimit retainsrealcountguard22result (neededheaderlimit256).
- BytesList Program/Reads/Step actualrfield/panop16/load/maxbguard70/iupdate;
  WhileActive genericallbodyoutcomes realwhileclockclamp; Loop actualread-only
  check finishes<=N+1clocks alloutcomes, normalN+alllimits, oractualSszErr70.
  Tail reali0scope+wholeloop+pairreturn/scoperestoreincludingarray0count0.
  BodyNormal actualVarListcallee+alltail, Records/copy/oldwords/countlimit/
  itemlengthlimits andnormalcost<=2floor(len/4)+2; enough2floor+4.
  Environment real4argABI; CallerNormal actualbyte-listcaller/resumption with
  allfacts and<=2floor(len/4)+3 callclocks; enough2floor+5.
- Successfuljoint input-bytes-list-caller-v1.log1431targets onlyallowedaxioms.
  Wholepayloadcaller/gasfromHeader recheckedafterVarListinterfacestrengthened.
- NEXT actualwitnesscontainerloop count3 rawoffsetreads/sszvalidation andthree
  byte-listcalls(st0:lim2^63-1,max1024;cd:max65536;hd:lim256,max1024), thenrootSI
  recordfields/constructoractualentry incldecodedbytes/heap/scratchroom. Need
  requestsdecoder(count5offsetloop+alloc80+fivefixedcounts) toreachwitnessfrom
  rootnormalrun. RevisitcredibleglobalQ/mutablecache/gas/heapcostfeasibilitybefore
  scalingfurther; actualtargetK/source-map equivalence stillunproved.
  Claiminfinity, nofullverifier. Account21%,0resetcredits watcheractive.

Global resource spending-gate revisit (2026-10-17):
- Exact offlineglobal-resource-pilot.py/json,2160bruteforceselfchecks passed.
  Sourcehashesrecorded, whole_bound=false. Jointcold*D+100Wgasmodel vs independent
  maxima; G380M/500M scenarios notexecutedgastheorems. One-mapstorage380M
 176097514634visits, acct122372849151; postwithdraw335544basekeys+120M
  warmwindow402652800000visits. No fullscore/certificatearithmeticclaimed.
- ActualGcoldAccount3000 (notexternalstandard2600), storage2100,warm100.
- RLPblock8MiBguard precedeswithdrawalprocessing; minwithdrawRLP25 yieldspaper
  Nwd<=335544 onceactualquotient/no-wrap proved. UnmeteredSSZearlierstill128MiB.
- htab_del backwardshiftlinear, notper-shiftfullreinsertion. Includehash/copy.
- Persistentheap31092374808bytes, hypothetical32bytes/query971636712queries;
  pairingnotproved. _decode_step RLParr allocations/compact path allocations;
  zeroextensionrejected; _decode_witness_node scratchrestoreonly; cache storage
  decodebeforetemporarykeyhashheapmark. Needallpersistentvsreleasedlifetimes.
- Decisioninconclusiveglobalgo unearned; no newactualcounterexample. BoundR7
  listsneededpremises. NEXT quantitativepilotactualsmallnonzerodivisor math
  fromrealUDivMod64-loop (neededactualcounts notjustshape/cost), withdrawalRLP
  length/cap thenjointgas/mapmultiplicity/heap Q. RootwitnessSSZ connectionstill
  open,butavoidblindlyscalinglocallemmaswhileglobalauditremainsincomplete.

Actual division math/withdrawal count field checkpoint (2026-10-17):
- UDivMod.ArithmeticBits exactinputbit,toNatshifted=2r+bit (r<2^63), quotient
  bitOR=naturaladditionfromalignment, low-input-remainder split. ArithmeticInvariant
  r<b,q%2^i=0,b*q+r*2^i+a%2^i=a, initiali64, actualnextQ/nextR preservation for
  b<=2^63 andfinalquot/remnaturaldivision. Ring/nlinarithusepermittedaxioms.
- StrengthenedactualLoop,Setup,Built,Call threadingconditionalarithmeticproof;
  bnonzero bodyreturnsrealq/r; forsmallb equalitytoa/b,a%b. No semanticchange.
  FixedList.Normal/Caller nowconditionalcount=length/size andlength%size=0 on
  normalreturn. AllactualSSZsizes32,44,68,76,116,184,192 satisfybound.
- PayloadWithdrawalNumbers actualvalidatedoffset2<=3, nowordsubwrap, count raw
  (le32input590-le32input570)/44 <=encodedExtent/44, its64bitwordexact.
  WithdrawalNormal retainsrealquot/mod44 facts. RemainingProgram/Execute actual
  finalcountcell56; TailNormal andAfterExtra/Allocated/Body/Caller carryexact
  countfieldrawquotient, whilekeepingrealgasfield88/copiedbytes/clockframes.
- Successfuljoint input-payload-count-field-v2.log1386targets allowedaxioms.
  NEXT actualRLP_be_len<=8 rounds purestateframe, actualword_encoded_len and
  header_len in[1,9], actualwithdrawal_rlp_len in[25,49]; thenactualblock_rlp_length
  min25perwithdrawal/no-wrap and8MiBguard=>Nwd<=335544. Globaljointgas/map/heap Q
  andcompiledtargetbound/source-mapstillmajoropen. Claim infinity,no fullverifier.

Actual RLP withdrawal phase checkpoint (2026-10-17):
- PureReturn/PureAssignReturn actual scalar call resumption with pure nonlocal
  frame, canonical saved caller binding and actual assignment validity checks.
- RlpLength/BeProgram,Step,Loop,Built,Call: real while(v!=0), shift8/countadd,
  <=8 rounds, actual function/body/caller, no arithmetic-loop surrogate.
- ShortOrBe/ScalarSizes real header and word size functions in[1,9], <=9 body
  clocks. ListHeader real ignored-result tailcall and real caller/assigncaller,
  <=10 body clocks. All lexical restoration and actual ABI included.
- WithdrawalProgram/Built/Call actual44-byte record3wordreads,3scalarcalls,
  payload21address+threepositivewordlengths, listheader+return. Size25..57,
  <=41body/42callclocks. Conservative57 retained, not advertised as sharp49.
- BlockProgram/Reads/Step/Loop exact fixed secondwhile: realpl48base/44stride,
  whileticks/call/wl+iassignments, copiedbytes preserved, <=43*N sourceclocks,
  natural25*N<=sum<=57*N, exact64-bitword no-wrap, otherlocals/control preserved.
- BlockSuffixProgram/BlockSuffix realtwo existing-hl assigning listheadercalls,
  totaladdition/return. BlockWithdrawalPhase composes actualloop+suffix; explicit
  initiali0/wl0, total<=2^32,count<2^31,copiedrecords+code premises. Encodedresult
  >=25*N and <=total+57*N+18, exactnativeword, <=43*N+22sourceclocks. Natural8MiB
  guard impliesN<=335544. Wholeblockprefix/entry andouterguard remainunconnected.
- Success input-rlp-withdrawal-phase-v2.log1127targets, permittedaxioms only,
  indexed4360modules6988facts. Failedsuffixv1 Option.map_some, v2sequencewrapper;
  phasev1 neededrflafterstateframe rewrite. Recoverylogsnotindexed.
- Next actualtransactionencodedlength<=recordlength+9 andtelescopingdecoded
  recordlengths, thenheader/transactionprefixbound andactualblockguard. Global
  jointgas/refunds/mutabletables/heapQ, originalmaprefinement andcompiledtarget
  K remainopen. Claim infinity; no fullverifier. Account23%,0resetcredits.

Actual transaction RLP phase checkpoint (2026-10-17):
- BytesSizeProgram/BytesSize/BytesSizeCall realrlp_bytes_encoded_len conditional,
  actualheadercall/pureframe andexistingelassigncaller; n<=128MiB =>natural
  encodedin[n,n+9] no-wrap, <=10body/11callsourceclocks.
- VarList.RecordSizes actualdecodedworddifferences telescope, aggregate<=slice
  length,everyitem<=slice. RecordPointers actualmappedpointercells/values and
  copiedfirstbytewhenitemnonempty; nofirstbytepremiseforzero-lengthrecords,
  noarrayreadforzero-countlist. sum_prefix_mono supplieseveryprefixbudget.
- TransactionProgram realfirstwhileandlogicalwraptest; AfterFirst includesel
  declaration,actualexistingelcallorlegacyrawbranch,tl/iupdates/scoperestore.
  Reads/Step includelengthload,conditionalfirstbyteload,fb/nscopes. Loop real
  signedtest/whiletickandallbodies, <=12*N sourceclocks, sum<=rawprefix+9*N,
  exact64-bitword/finali/tl andotherlocal/controlframe.
- TransactionDecoded instantiatesallmemory/bytepremisesfromrealRecords+HeapInput,
  sums<=slicelen+9*N<=436207564 atactualencodedextent<=134217712, N<=len/4.
- AfterTransactionsProgram/AfterTransactions literalfirstlistheadercall,
  total/ommersadds,actualnwdcell56load,wl0scope/i0resetandwithdrawalphase.
  TransactionPhase provesexactsubtreeoffixedblockbodyandcomposesbothloops
  throughreturn: <=12*Ntx+43*Nwd+33sourceclocks, encoded>=25*Nwd, exactword.
  Explicitprecedingheaderlen<=2^31,phaseentry/copy/domain/code/cells remain.
- Successfuljoint input-rlp-transaction-phase-v2.log1337targets, onlyallowed
  axioms,index4374modules7012facts. Failedlogsreflectliteralbitwisecompute,
  bindoverwrite/restorescope,simpaliases,firstbyteaddresssetWidthandscopeof
  one-linetactic; failurelogsnotindexed. Resourcesremainlow,disk58%/124GiBfree.
- NEXT actualencode_headerboundedlengthandentryinitialization/wholeblockcaller,
  thenactual8MiBguardcap. Avoidclaimingunconditionalglobalwithdrawalcapbefore
  thosepremisesareclosed. Globalgas/refunds/mutablemapmultiplicity/heapQ,
  originalimmutablemaprefinement/targetcertificate remainopen. Account24%,0
  resetcredits; claimedKstillinfinity, nofullverification.

Actual encoding writer checkpoint (2026-10-17):
- RlpWrite.PutBeProgram/Loop/Built/Call realreversei--, st8(dst+i,v),v>>8,
  whileunsignedpositive andreturn0. ExactNbody/N+1callsourceclocks; actualmemory
  writesretained, outsidealignedstorewordsframe, real3argABI/ignoredcaller.
- LengthTail/Forms realtagstore+put_becall+return andrealbe_lenprefix/scope;
  shortformstore/return andlongform<=18bodyclocks/<=9bytes. HeaderWrite and
  WordWrite completeactualfunctionsforall64-bitvalues; sizein[1,9], memory
  frameoutside9bytes. RealHeaderWriteCall declaration/tailcalls andWordWriteCall
  declaration/existinglocalassignment includeactualmetadata/shapechecks and
  callerstatewithwrittenmemory. MemoryReturn genericactualresumption/frame.
- BytesWriteGeneral actualheadercall+fullCopyGeneral.memcpy+return/scopes,
  n+1<=encoded<=n+9,<=n+20sourceclocks. BytesWriteProgram specialn1srcbyte-read,
  b<128directstore/return, elsebscoperestoredunchanged. BytesWriteBuilt whole
  fixedencoderforalln<=134217712, retainsactualmemory/frame,no-wrapsizeword.
  Access/mapping/runtimepremisesexplicit; memcpyallowsarbitraryalignment/overlap.
- Successfuljoint input-rlp-byte-write-built-v1.log1139targets,index4388modules
  7038facts,allowedaxioms. FailedlogsnormalizationofwordaddressAC,typedstate
  aliases,let-RHSparenthesesandUInt8.sizeclosedbound; noneusedasevidence.
- NEXT bytewriteractualcallerthenrealheadersequence: u256_byte_length/limb/min
  writers, encode_headerbuffer1024andallfields/pincrements, actualblockprefix
  callerand8MiBguard. The resultingNwdcapstillconditionaluntiltheseclose.
- Useraskedoverallestimate: about35%with25-45%lowconfidencerange, wholebranch
  effortjudgment, notfilecount/proofpercentage. Majorremainingglobalgas/heap/
  workpotential, mutablemapmultiplicity/queryQ, originalmaprefinementandcompiled
  targetcertificatepreventcallingtheprojectmorethanhalfcomplete. Claimstill
  infinity; nofullverifier. Account24%,0earnedresetcredits,watcheractive.

Byte writer callers and U256 length checkpoint (2026-10-17):
- BytesWriteCall real3argtupleABI, lexicaldeclaration/existinglocalassignment
  withactualwrittenmemoryandoutside-rangeframe; Access/Codes bundlesretain
  explicitmapped/copy/runtimepremises, sourcebody<=n+20/caller<=n+21clocks.
- BitLengthProgram actualbit_length64sixstages32,16,8,4,2,1: truebranchupdates
  n/x, falsebranchskip. Inductivebitrangehalving(count+shift, x<2^shift) without
  nativeaxioms. Built completeactualfunction<=64 andpureframe0bodyclocks,
  actualunarycaller1clock. Notusedasmathematicalbitlengthcorrectnessyet, only
  bound/actualexecution neededforencodingcost/size.
- U256Value actual4-wordValueHOL.rStruct tuple/shape, realfieldreadsfiniteindex
  andsingle-tuple-argcalleeenvironment. U256BitsSegment realbit64calls plus
 192/128/64addition oractualtailcall; scanprovesactualupperlimbchoice/return
  <=256, pureframe1bodyclock. Wholefunction/scopedcaller2clocks.
- U256ByteLength actualcalland(n+7)>>>3, checkednaturalno-wraparithmetic<=32,
  pureframe2body/3callclocks. All6conditionalstagesandactualtupleABI included.
- Successinput-u256-byte-length-v2.log1146targets, permittedaxioms only.
  FailuresExpHOL.rfieldlowercase,opaquecombshapeEqneedshapeEqHOL_eq_true,
  literalFincoercionrfl, congrArgexpectedtype/offsidecallerargument; fixed.
- NEXT u256_limb0body/1call,puretuple+scalarABI, thenactualu256_to_be_min
  loop<=32iterations(2clocks/iter), realrlp_put_u256alloc32/heaprestore/copy;
  thenwholeencode_headerandblockprefix/guard. No newfullK/globalgoearned.
  Account25%,0resetcredits. Claim infinity,no fullverification.

Actual minimal U256 writer and heap-scope checkpoint (2026-10-17):
- U256Limb completeactualconditionalreturnscan andtuple+scalarABI/scopedcaller,
 0body/1callclock, purestateframe. Returnedwordexistenceissufficientforwriter
  execution; exactmathematicalselectedlimbvalueisnotanassumedpremise.
- U256MinProgram realposition=len-1-i no-wrap, realmaskedshiftamount<64 using
  WordBits.mask7, actualbyteexpressionread. Step actualposdeclaration/limbcall/
  byte-store/increment andbothrestoredscopes, exact1callclock. Loop actual
  unsignedtest/whiletick, <=32rounds, exact2*roundsclocks, onlyilocalchanges,
  memoryframeoutside32destinationbytes. Built wholeactualbyte_lengthcall,
  loop/return/scopes: size<=32, <=67body/68callclocks, actualwrittenmemory.
- HeapScope actualheap_markzeroargcallee/caller, releaseglobalheap_ptrassignment
  andignoredcallerwitholdsavedcallerlocals. Eachcall1clock; releaseexplicitly
  updatesonlyheapglobal, markpure. Neitherassumesheapallocation/lifetimefacts.
- RlpWrite.Access bytes_read_exists foractualmappedwordandbytes_access deriving
  everybyteencoderpremisefromordinarydomainandtwoAllocatedBytes.Arenaextents,
  includesempty/singleitemsandarbitraryalignment/overlapcopy. Sourcecontents
  arbitrary, noassumedbytevalueorcopyoracle.
- Success input-rlp-write-access-v2.log1154targets, onlypermittedaxioms. Failed
  minreadsnormalizedshiftguardandAndOpinstance neededstagedeval/rfl; allfixed.
- NEXT actualrlp_put_u256 heap_mark+alloc32+u256min+byteencoder+heap_release+
  return/scopes; expected<=124body/125callsourceclocks,size<=41. Thenreal
  encode_headersequenceandbuffergeometry. Cheap arithmetic PLAN (notyetproof):
  optionalcurrentheadermax14bytestringfields(rawtotal636)+7scalarfields+2U256;
  byteboundsn+9,word9,U25641 implypayload907, list<=916bytes; buffer1024fits.
  Bytecallsraw636+14*21=930,scalar7*19=133,U2562*125=250,listlength11,
  alloc1,listwrite20 =>plannedwholeheaderbody<=1345/call1346sourceclocks.
  Needderiveallrealfieldloads/copyextents, sequence/restoration, extra<=32,
  bufferincrementation/no-wrap andtemporary32bytesreusedbyheap_release. These
  areplannednumbers, notclaimedwholeheadercosttheorems/globalK.
- Rootblock8MiBguard/phaseentry, gas/refunds/mutabletables/heapQ andoriginalmap/
  targetcertificate remainopen. Account25%,0resetcredits, claim infinity.

Actual complete rlp_put_u256 checkpoint (2026-10-17):
- U256PutProgram exactfixedfunctionASTandCodes; restore_global provesreal
  doubleheapmapupdatebacktosavedexistingvalueequalsoriginalmap.
- Prepare actualheap_mark+alloc32callerclock2, realreturnedtmp/markbindings,
  heaproundedcursorfield/control. Supportsanyvalidcursor, alignmentnotneeded
  becauseactualmemcpy/writershandleunalignedaddresses.
- Suffix realminwriter/byteencoder/heap_release/return/scopes, <=122source
  clocks, encoded1..41. ActualordinaryArenaextentsderiveeveryaccess. Retains
  exactmemoryandselectedheapglobalupdate, outsideoutput41/temp32frame.
- Built entireactualfunction <=124bodyclocks, no-wrapencodedword, **exact
  originalglobalsrestoration** viarealreleasecall, memory/controlframe. Calls
  actualscalar+tupleABI, lexicaldeclandexistinglocalassignment, <=125total
  sourceclocks, actualwrittenmemorykeptinthecanonicalcallerstate.
- Successful input-u256-put-call-v1.log1159targets, permittedaxioms only.
  Onefailedprefixrecordnewlineindentationfixed. Fullverificationnotrun.
- NEXT wholeencode_header. Plannedconservativecurrentfieldboundsconfirmed
  fromliteralAST: firstbytes8/32; restbytes16/32,24/20,32/32,40/32,48/32,56/256;
  wide64;words96,104,112,120;extra128/len136<=32;bytes144/32,152/8;wide160;
  bytes192/32;words200,208;bytes216/32,224/32;optionalbytes232/32+word240.
 21base+2optionalfields; headerstruct248bytes. Basepayloadmax857/cost1241,
  optional50/cost72; totalpayload907/fieldcallcost1313. Finalalloc1,listlen11,
  listwrite20 giveplannedbody1345, encoded<=916in1024buffer. Stillnotwhole
  functionproof: needoldheadercellframebelowfreshbuf, everyfieldargumentread,
  actualrightnestedcall/incsequence, conditionaloptionals, heapbuf+1024stable,
  temporary32room/no-wrap andfinaltuple/scopes. Thenactualblockprefix/8MiBguard.
- Currentglobalfeasibility/source-map/targetcertificateopen; nofiniteK. Account
 26%,0resetcredits. Useroverallestimate35%(25-45%lowconfidence)stilljudgment,
  notchangedbycountinghelpermodules. Continuedaftercheckpoint, nostoppoint.

Actual header field sequence checkpoint (2026-10-17):
- HeaderEncoding.Program exactliteralencode_headerAST decomposition, actual
 21base+2optionaldescriptors, rightnestedcall/incsequence, firstwdeclaration,
  optionalterminatingincrementandsuffixtuple. Kernelcheckedliteralfieldbudgets
  base857/1241(size/callclocks), optional50/72; fullheadernotyetassembled.
- Context Geometry header248bytesbeforefreshbuffer, alignedbufferand1056room;
  ordinarydomain, preservedmemorybelowbuffer, actualhlocal/heapbuf+1024.
  Metadatawordcellsderiveactualmappedloadvalues; before_away provesoldcells
  cannotmatchactualbyte/wordwriteraddresses, includingalignedstorefootprints.
- Reads realonewordandquadcomb4 loadsfromoriginalmetadata, arbitrarybitvalues.
  FieldPost realwriter+w/padvanceandrightnestedresumption; exactp/wlocals,
  otherlocals/frameandContextreestablishment.
- FieldBounds/FieldRun byte/scalar/wide/extraactualcalls deriveallargumentsfrom
  metadata, extentsfrombuffergeometry, sourcebyteaccessfromArenas; U256temp32
  heaproomandmetadataframeexplicit. Eachfieldpaidsourceclocks/maxbytes isits
  owndescriptorallowance. Fields actualfulllistcomposition preservesContext,
  returnsnatpositionbetweenstartandstart+sizes, paid<=costs, canonicalframe
  andscalarlastw, otherlocals, arbitrarycontinuationresumption.
- RlpWrite.ListWrite actualtailcallrlp_write_header(...,192,...), wholebody<=19,
  realignoredcaller<=20sourceclocks, actualmemoryandoutside9byteframe.
- Successful input-rlp-list-write-v1.log1167targets, onlypermittedaxioms.
  ContextcellwordAtunfold, scalaraddresshypnormalization, Fin3.valrfl and
  advancewrapperforrw fixedinfailedlogs, notusedasevidence.
- NEXT HeaderEncoding.Optional twoactualoptionalfields+currentwordconditional;
  suffixpayload/startnativearithmetic,listlen/listwriter+tuple/scopes; initial
  alloc1024/p9/firstbyteswdecl andwholeheaderfunction/caller<=planned1345/1346,
  thenactualblockprefix/8MiBguard. HeaderFacts requirebytepointerArenas and
  extra<=32 fromrealbuilder; rootreachabilitystillopen. Sourcestepsarenottarget
  steps; globalgas/heap/potential/maprefinement/targetK remainunproved.
- Account26%,0resetcredits; claim infinity. No fullverification, workcontinues.

Whole actual header/block length and payload guard checkpoint (2026-10-17):
- HeaderEncoding Optional proves both real optional writers, literal terminal
  increment, current-flag memory read and skipped branch. SuffixArithmetic
  proves natural pointer subtractions; Suffix runs payload subtraction, actual
  list-size/list-writer calls, tuple return and all scopes. Actual memory is
  preserved below the fresh aligned buffer, including aligned word footprints.
- Rest composes all remaining base fields, optionals and suffix. First handles
  the distinct first w declaration, its actual byte arguments/write, p update
  and remaining continuation. Whole executes alloc1024/p9/first/rest/all
  scopes; encoded size1..916, <=1345 body clocks, actual heap advance1024.
  Call checks the actual unary-argument/two-word-return ABI, <=1346 clocks and
  canonical memory/globals/caller-local effects. Frames derives copied-input
  and actual decoded-record preservation from old memory and natural placement;
  empty slices have no positive allocation or record-read requirement.
- RlpLength EntryProgram is the exact fixed block AST with bundled real code
  lookups. EntryDeclarations derives actual header tuple field, transaction
  pointer/count reads and zero loop counters; Data.of_old_memory transfers the
  concrete decoded input and payload cells. WholeBlock executes actual mark,
  encode_header, release and both loops. It restores original globals exactly,
  returns >=25*Nwd without wrap, upper436208508+57*Nwd, and consumes at most
 12*Ntx+43*Nwd+1381 body clocks. BlockCall adds the real ABI/call clock.
- BlockGuard identifies the literal payload_header 8MiB guard as its actual
  subtree. It checks pass/raise branches and proves the complete actual block
  call followed by successful guarded continuation implies Nwd<=335544.
  This no longer assumes the preceding encoded-header-size bound.
- Entry premises remain: actual decoded Records/HeapInput/payload cells,
  byte-pointer Arenas and extra<=32, header before fresh buffer and1056room,
  ordinary domain, code and clock affordability. Establishing these at root,
  whole gas/heap/query potential, original-map refinement and target K remain
  open. Source call/loop clocks are not target machine transitions.
- Successful closure input-block-guard-v3.log1393targets, only allowed axioms,
  6.06s wall, maximum child RSS2025680KiB; resource sample host use~1.9GiB,
  disk58%. Earlier targeted failures fixed source-clock alias normalization,
  multiline record syntax, pair caller clock subtraction, explicit local-key
  inequalities and AST guard reduction; failed logs are not proof evidence.
- Indexed4429modules/7139printed facts. Incremental policy passes61292entries,
 2252515261bytes; not isolated verification. claim infinity. Account27%, no
  reset credits. User overall estimate35%(25-45%, low confidence), including
  all work above main, remains a judgment rather than file-count progress.
- Continue joint gas/refunds/mutable-table/heap-Q spending gate and root decoder
  entry connections; no whole-program go or finite K has been earned.

Actual state-gas refund/refill conservation checkpoint (2026-10-17):
- GasBudget.Frame real ev-global address/load helpers, literal offset separation
  and regularBudget=gas_left64+regular_used184+outstanding_spill192.
- Refill executes actual message load and three stores: liquid+=spill,
  state-left=message reservoir, spill=0, return/scopes. Caller costs1source
  clock, body0. Reservoir read cell must differ from first liquid write.
- Minimum executes actual unsigned two-argument min, proves its natural minimum,
  real ABI and scoped caller, no body clocks/one call clock.
- Refund executes actual spill load/min call and all three stores: liquid gets
  min(amount,spill), spill loses it, state-left gets the remainder. One body
  source clock. Both actual ignored callers check, retaining changed memory and
  unchanged control/globals, and preserving regularBudget if liquid+spill<2^64.
  Actual amount/cell/runtime/clock premises explicit. No whole-run gas bound.
- Successful joint closure gas-refund-calls-v1.log1102targets, allowed axioms,
  7.73s wall, maximum child RSS1908472KiB; disk58%, host~1.3GiB afterward.
  Failed draft fixes: exact BitVec.add_right_inj lemma, typed mapped-cell alias,
  opaque wordOp simplification, normalized record-memory projections and min's
  empty-locals clock clamp. Failed logs are not evidence.
- Index4434modules/7155facts; incremental policy61298entries/2252545515bytes,
  passes with infinity claim. All changed sources indexed. Account27%, no
  reset credits. No full verifier or baseline audit run.
- Gas audit: CALL/CALLCODE charge11300 nonzero-value overhead and subtract
  forwarded gas including2300 stipend from regular-used; raw cumulative
  charge_gas amounts therefore are not net regular consumption. Actual
  calculate_intrinsic_cost returns regular,0,floor; process_transaction regular
  block accounting is before ordinary refunds. Need actual state-charge,
  child transfers, stipend-payment/no-wrap and signed state/block conservation.
- Refreshed global-resource-pilot source hashes include evm_calls and tx;
  2160small optimizer self-checks pass, whole_bound/certificate remainfalse.
  Whole header/block guard result is recorded with root entry premises open.
- Continue charge_state_gas and child-call transfers, then aggregate joint
  gas/table/heap accounting and root entry refinement; finiteK still open.

Actual state-gas charge success/failure checkpoint (2026-10-17):
- AddExact actual add_sat on the no-overflow branch, exact sum, pure frame and
  real two-argument caller. Fits premise state_left+gas_left<2^64 is explicit.
- StateChargeProgram exact fixed AST, all tests/branches, real pool loads and
  stores; Pools contains actual ev, mapped gas/state/spill words and values.
- StateChargeSpill actual deficit declaration, state zeroing, regular debit,
  spill addition, return and local restoration. StateCharge composes both
  actual affordable paths, real add_sat call and outer declarations. Body
  consumes0 or1 source clocks; exact memory is the branch's actual store list.
- StateChargeBudget proves natural gas_left+regular_used+spill conservation
  under affordable and gas_left+spill<2^64. Actual original regular counter is
  untouched. StateChargeFailure executes real unaffordable add_sat/test/raise,
  no memory writes, exact one body call clock. Call summaries cover successful
  ignored caller<=2clocks and failed caller exact2, actual EvmErr4 propagation.
- Success gas-state-charge-call-v1.log1109targets, all permitted axioms,
  4.57s wall, max child RSS1884856KiB. Fixed draft signed/unsigned notLower test
  simplification and list-membership normalization; failed logs not indexed.
- Index4441modules/7167facts. Policy passes61305entries/2252579761bytes;
  infinity claim, no full verification. Host1.8GiB during last build, disk58%.
  Account28%, reset credits0. Reproducible pilot metadata refreshed with actual
  charge log and no-wrap premises;2160optimizer checks pass, global flagsfalse.
- NEXT child regular-gas transfers, stipend payment and frame halt, then signed
  state/block conservation, joint mutable-table/heap-query bounds, root input
  entry, original-map/compiler/target/fixed-certificate connections. These local
  conservation summaries do not yet prove380M aggregate gas or finite K.

Actual halt and child-error gas return checkpoint (2026-10-17):
- Halt exact fixed three-store AST/body/caller, regular-used+=liquid,
  liquid=0, EV_ERROR160=err. Source body0/caller1 clocks. Natural regular
  budget preserved if liquid+used<2^64; source cells/code explicit.
- ChildErrorProgram actual fixed incorporate_child_on_error body, frame amount
  views and shared Ready (actual globals/local, mapped parent/child words,
  values, cross-frame separation). Actual summed-field store/read helpers.
- ChildError executes all parent liquid/state/regular-used additions, preserving
  later parent and child reads through real stores. Its natural budget equation
  says resulting parent budget + old child outstanding spill = old parent +
  old child budgets. Thus parent result cannot exceed their sum; after refill
  the omitted child spill is zero. No-wrap liquid/used sums are explicit.
- Actual unary ignored caller executes in1source clock, retaining exact memory
  and control frames and the same budget equation. No whole call-tree claim.
- Successful gas-child-error-call-v1.log1113targets, only permitted axioms,
  4.24s wall, max child RSS1875564KiB. Halt draft fixed missing shapeToHOL
  reduction; failed log not evidence. Index4445/7179. Policy renewed; infinity
  claim, no full verifier. Account28%, credits0, host/disk within limits.
- NEXT successful child repayment prefix and forward/stipend debits, actual
  regular-charge source bridge and global signed state/block accounting; joint
  table/heap-query work and original-map/target certificate remain open.

Actual Pan regular-gas charging checkpoint (2026-10-17):
- RegularCharge exact fixed source AST, actual liquid load, affordable guard,
  liquid debit and used-counter increment, return and gl scope. Out-of-gas
  branch raises EvmErr4 before any pool write. No body calls/loops.
- Quantitative real written memory preserves regularBudget; liquid native debit
  and used native credit equal amount exactly under affordable and
  liquid+used<2^64. Actual successful ignored caller costs1Pan source clock;
  failed caller exact1 with unchanged memory/control and exception propagation.
- This supplements the existing compiled Stack charge summary. Their clocks
  belong to different semantics; no whole-run compiler/target connection or
  positive-charge coverage is inferred from these local summaries.
- Successful gas-regular-charge-call-v1.log1115targets, permitted axioms,
  4.66s wall, max child RSS1888656KiB. No failed draft builds in this pair.
  Index4447/7185; policy61311entries/2252614026bytes, infinity; no full verifier.
- Continue successful-child repayment and forward/stipend contracts, global
  signed state/block accounting and joint gas/table/heap query budget.

Actual call-gas calculator and forward-prefix checkpoint (2026-10-17):
- U256Zero actual four-limb OR/zero predicate, equivalence to all limbs zero,
  actual tuple ABI/caller, pure/no body clocks. Fixed opaque OrOp.fold bridge.
- CallGasProgram exact fixed calculator AST; actual cap=left-(left>>>6),
  natural cap<=left, capped request=min(request,cap), stipend0or2300. Requested
  gas can be any64-bit word. CallGasCap real mutable clamp/declarations/return.
- Inputs preserves real five input locals through actual temporary bindings.
  Actual zero need computation executes add_sat(0,0), skips true shortage test,
  performs exact available subtraction and cap. CallGas whole body executes
  u256_is_zero, stipend declaration/assignment, actual add_sat, all scopes and
  pair return; exactly2Pan call clocks and pure state frame. Actual five-input,
  pair-return caller executes in3clocks, canonical caller and lexical restore.
- ForwardBudget no-wrap counter subtraction and stipend-funding arithmetic;
  real used-counter word subtraction preserves other gas cells. ForwardPrefix
  executes actual charge_gas debit call plus actual used-counter subtraction,
  then resumes arbitrary continuation in canonical memory/clock state. Under
  funded stipend and no-wrap entry, parent new budget+forwarded child seed=
  parent old budget. Exactly1Pan clock from the charge call.
- ForwardSites proves literal prefix membership and zero memory/extra-cost
  calculator arguments in CALL/CALLCODE/DELEGATECALL/STATICCALL. Opaque
  progToHOL equations require simp, not dsimp/rfl alone. Fixed reserved prefix
  identifier, doc-comment/set_option placement and full AST conversion in
  failed drafts; failed logs are not indexed.
- Success gas-forward-sites-v6.log1168targets, permitted axioms only,
 8.58s wall, max child RSS2158612KiB; host~1.4GiB afterward, disk58%.
  Index4456modules/7210facts; policy61320entries/2252659478bytes, infinity.
  Account29%, no reset credits. No full verification or external actions.
- Pilot metadata records forward log/funded/no-wrap premises;2160small arithmetic
  optimizer checks pass. No380M total, global go, K or target certificate earned.
- NEXT actual up-front fee funding (general saturating-add lower bound),
  successful-child spill repayment prefix and protected gas cells through its
  log/delete-set merge. Then full call-tree/signed-state/block conservation and
  joint table/heap-Q work; root initialization/map/compiler/target still open.

Actual up-front value-fee funding checkpoint (2026-10-17):
- SaturatingAdd complete actual add_sat, both overflow/exact branches and real
  caller. Result>=first argument unconditionally, so access+11300 with
  access<=3000 gives actual fee>=11300 even if memory cost saturates.
- ValueFee exact two-input add_sat arguments and actual lexical need/charge
  prefix. Successful real charge retains canonical caller memory/clock and
  credits used>=11300, hence funds2300. Actual unaffordable fee raises EvmErr4
  before continuation with unchanged memory/control. Both calls included,
  exactly2Pan clocks. Source local/pool/code and natural no-wrap premises
  explicit; arbitrary following continuation and saved need restoration checked.
- ValueFeeSites exact prefixes in CALL/CALLCODE and actual zero value supplied
  by DELEGATECALL/STATICCALL, with zero-stipend equation. This addresses the
  source of the funded-stipend premise, though full intervening-helper/global
  frame and successful-child invariants still need assembly.
- Success gas-value-fee-sites-v1.log1171targets, only permitted axioms,
 7.39s wall, max child RSS2133244KiB. Fixed expected-type recursion on unsigned
  lower-bound coercion and literal charge/entered wrappers for rewriting;
  failed logs not evidence. Index4459/7220; policy61323/2252675043bytes,
  infinity claim, no full verifier. Account29%, credits0; resources safe.
- New conditional spending observation: nested map merges must respect each
  root's regular cap and actual63/64 forwarding, rather than multiplying all
  global gas by depth1024. For recurrence g'=(g-100)-(g-100)//64 and hypothetical
 5000gas per produced delete key, a single chain max L*floor(g_L/5000)^2 is
 420268032 at L32,3624keys for30M root, and131349632 at L32,2026keys for
 16777216 root. This is exact exploratory arithmetic, not a runtime/forest/
  table-work bound. Actual fee/child/frame/source-root premises remain open.
  Next prove the uniform decay algebra, then a small reproducible conditional
  nested-resource pilot before scaling remaining global/map proof work.
- Main open: successful child spill repayment and log/delete merge frames,
  complete parent/child/initialization trace, signed state-debt/refund ledger
  and block counters (ordinary refund is not deducted from BO_GAS_USED), joint
  table/heap-Q work, root decoded entry, original-map/target/certificate.

Conditional nested decay and scenario checkpoint (2026-10-17):
- NestedDecay checks exact cap monotonicity, stipend compensation, uniform
  child<=capNat(parent-100) from explicit access/value/available premises and
  actual calculator values; 64*(child+6237)<=63*(parent+6237), geometric chain
  inequality and root<=30M depth<=538. Literal power comparison uses ordinary
  kernel decide. Actual fee/root/frame premises on every runtime edge open.
- Success gas-nested-decay-v1.log1172targets,4.58s,max child RSS1914976KiB,
  permitted axioms. Index4460modules/7228facts; incremental policy succeeds,
  61324entries/2252679867bytes, infinity, not a full verification.
- Reproducible nested-resource-pilot.py/json exact arithmetic explicitly
  reports whole_bound/certificate/runtime_work_bound=false. Single-wave and
  earlier-key scenarios give131414464 units for16M root,420268032 for30M.
  Greedy repeated waves returning unused gas and retaining earlier keys at
  every ancestor freely reach919662004 units (depth214,92waves) and3321693864
  (depth236,137waves). These are relaxed scenarios, not reachable attacks or
  arbitrary-schedule/forest maxima. They prevent using the single-wave bound
  as an aggregate. Extra setup/CREATE costs, actual key events, hash probes,
  rehashes/copies and prices remain unproved.
- Overall progress estimate to user about35%, rough25-45%, by remaining proof
  obligations, not file counts. Claim still infinity; global bound and final
  certificate open. Account30%, no reset credits; host/disk within limits.
- Continue successful-child spill repayment and protected gas cells through
  logs/table merges, whole trace/initialization and signed state/block ledger;
  numerical pilot has not earned a whole-program feasibility go.

Successful-child gas prefix and conditional forest checkpoint (2026-10-17):
- Repayment actual declaration, mutable minimum, three stores and arbitrary
  continuation/scope restoration checked. Gas+used+spill preserved. Failedv1
  fixed destructured evaluator pair losing its equation; v2 success.
- ChildSuccessProgram exact fixed AST decomposition separates literal
  child-error call, spill addition, repayment and real log/delete-set suffix.
  ChildSuccess actual prefix executes with exact memory/control and explicit
  frame separation. Under combined budget<2^64, parent resulting regular budget
  equals both previous budgets combined. No source clocks beyond actual child
  error call1; later suffix not priced or assumed to preserve gas words.
  Failed drafts fixed Option.map normalization, explicit write aliases and
  memory projection normalization before omega. Success gas-child-success-v4
  1116targets,14.39s,max child RSS1892748KiB, permitted axioms only.
- MergeBudget counting model handles arbitrary sequential/nested call forests,
  unlike single-wave scenarios. propagation<=depth*productions; weighted work
  <=(maxKeys+1)*maxDepth*totalGas/productionPrice under paid-production/depth
  premises. This does not assume sum of initially declared root gas<=block gas.
  Literal maxKeys6000,depth538,total380M,price5000 gives245368888000units.
  Hypothetical3552/unit gives871550290176000, before rehash/copy/otherwork.
  Actual occupancy, production payment, forest/merge coupling and target prices
  unproved. Local theorem is conditional; no global gas allowance or K earned.
- Success gas-merge-budget-v1.log1173targets,4.43s,max child RSS1926756KiB,
  permitted axioms. Index4464/7236. Policy61328entries/2252704190bytes, infinity.
  Host1.3GiB used/29GiB available,disk58%,124GiB free. No full verification.
- Continue protected frames/initialization/state-debt ledger and joint table/Q
  gate. Trie decode queries can be paired with parent slice-array slots
  (16bytes/slot, branch16of17 or extension1of2), rather than assuming every
  query immediately allocates32bytes. Root/code queries need separate budgets;
  heap lifetimes/release and event coupling remain open, not a proven count.

Storage debt guards and block accounting checkpoint (2026-10-17):
- U256Eq actual four-limb xor/or equality body, tuple ABI/environment/caller
  and equality equivalence checked. StorageDebt value transition exactly
  balances state charge/refund against debt when original zero/current nonzero.
  Conditional ledger telescopes; zero-start refunds<=charges. Dropping debt
  without refund is permitted; rollback/committed-trace projection is unproved.
- StorageTests literal state-gas/refund prefix selected from fixed op_sstore;
  exact three-condition Boolean evaluation checked for arbitrary actual0/1
  locals. StorageClassify links actual equality/zero outputs to those guards
  and the97920 per-slot debt equation. It does not execute every SSTORE helper
  or establish backend honesty, state journal, created-address original values
  or gas reservoir correspondence. Destroy/rollback/creation need separate
  consistent-value/ghost ownership invariants.
- gas-storage-classify-v3.log1164targets,4.44s,max child RSS1904088KiB,
  permitted axioms. Failed drafts fixed classical decision instances in
  theorem statements, closed OR zero normalization and Bool.decide_and name.
- BlockAccounting conditional natural pool equation yields BO regular charge
  max(intrinsic+used,floor), with explicit nonnegative state accounting. Passed
  reservation bounds completed counter and unfinished final transaction work;
  aggregate uses charged work, not sum of initial root gas. Source TX_BASE is
 12000 (self-transfer recipient cost may be0), giving conditional completed
  count16666 at200M. Actual intrinsic no-wrap/floor lower bound remains open.
  Actual BO_GAS_USED store selected from fixed process_transaction and real
  store execution/no-wrap addition checked under explicit local/cell/bound
  premises; full process/check_transaction/pool/state linkage remains open.
- Success gas-block-accounting-v1.log1165targets,5.84s,max child RSS1967500KiB,
  permitted axioms. Index4469/7263; policy61333entries/2252730199bytes, infinity.
  No full verifier, global finite K or overall feasibility go earned.
- Next actual mutable table lookup/ownership invariant and protected gas frame,
  plus root init and backend/state-ledger coupling; continue joint table/heapQ
  costs and original/radix/target composition. Local algebra cannot substitute
  for the full reachable-state invariant.

Original mutable32-byte table scan checkpoint (2026-10-17):
- MutableTable.Probe exact bitmask/modulus and masked increment for any
  power-of-two capacity below2^64. Distinct occupied prefix slots before a
  cycle, count bound from order-list coverage, and empty within count proved
  without hash randomness or cryptographic assumptions.
- FindProgram exact fixed htab_find_slot AST; actual used-byte condition and
  masked increment reads checked. FindStep32 actual32-byte comparison argument
  expressions and real fixed memeq environment/body/caller at any alignment;
  actual eq guard early return or increment, scope restore, memory/control
  frames and<=5call/comparison clocks. No comparator run is a premise.
- Chain32 concrete memory views along the probe path, exact first-match answer.
  Actual while executes in<=6*occupied-prefix clocks (one while plus<=5call),
  including early matches and empty stop. FindTail32 actual absent-cap return.
  FindChainBuild derives an executable chain from actual prefix loads/views;
  first empty derived using binary used-array and occupied-order coverage.
  MaskedPath links indices to the exact word increment; full scan's bound
  <=6*order.length follows from physical table premises, with pure memory.
- Successful mutable-masked-path-v2.log1107targets,4.44s,max child
  RSS1898920KiB, only permitted axioms. Index4476/7284. Failed drafts fixed
  implicit nodup_range parameter, UInt8.size type annotations, local-frame
  transport, evalHOLFinite wrappers, typed returned constructors, let/projection
  simplification and explicit pathIndex unfolding. Failed logs not indexed.
- Policy61341entries/2252767802bytes, infinity. Host1.4GiB used/29available,
  disk58%/124GiB free; account31%, reset credits0. No full verification.
- Open: actual header/hash/caller setup; general20/52/60-byte comparison;
  constructors/mutators preserving used/order/key/heap ownership and lookup
  semantics; original/radix dictionary refinement; protected gas frames and
  full global gas/state/source/target/certificate. Pan clocks are not target
  prices; this result neither establishes a finite K nor a global go.

Complete original32-byte find/hash/caller checkpoint (2026-10-17):
- HashAligned32 exact fixed aligned fast path from four mapped/stored words,
  including every xor,shift,multiply and return. HashCall32 actual outer h/w
  declarations/scopes and two-argument ABI/caller; body0/caller1 clocks.
- HashUnaligned32 actual32 byte reads and expanded LE macros, same full hash
  arithmetic and pure0-clock core. HashWordBytes reconstructs each actual word
  from eight byte extractions. HashMemory32 proves packed word/byte roundtrip,
  uniform actual byte-key hash at all alignments, whole body and real caller.
  Result depends only on the key's bytes; no distribution assumption.
- FindHeader all five real header reads/declarations and full lexical restore
  stack. FindPrepared actual post-hash/index locals, mask/start numeric bridge.
  FindAligned32 whole aligned original htab_find_slot, then FindMemory32 whole
  original body at every alignment. FindCall32 real two-argument environment/
  caller and canonical continuation. Body<=6*order.length+1,caller+2 source
  clocks. Actual physical header/used/key/query byte views, covering order list,
  room, power-of-two capacity, code and clock premises are explicit. No hash
  or comparator execution is a premise.
- Important boundary: order.length is the length of the supplied covering
  order list. Source HT_COUNT/order-array correspondence and maintenance by
  constructors/insertion/growth/deletion/rollback are not proved. Do not label
  the bound an unconditional HT_COUNT bound. Dictionary/last-wins refinement
  and general20/52/60-byte keys remain open; Pan clocks are not target pricing.
- Successful closure mutable-find-call32-v1.log1119targets,4.64s,max child
  RSS1904120KiB, permitted axioms. Whole general-body success
  mutable-find-memory32-v1.log1118targets,9.50s,max RSS1906852KiB. Aligned whole
  body mutable-find-aligned32-v2.log1112targets,6.96s,max RSS1907544KiB.
  Unaligned final mutable-hash-unaligned32-v4.log1113targets,6.85s,max
  RSS1930300KiB. Earlier unaligned draft ran7m12.19s then failed on a missing
  normalized pointer+0 read; fixed to a direct pointer read. Other failed
  drafts fixed declaration recursion wrappers by separating actual core and
  scopes, HOr/OR normalization, explicit setWidth numeric equality, declaration
  doc placement, finite literal-name distinctness and canonical frame aliases.
  Failed logs not evidence; final committed sources have no proof holes.
- Index4486/7304; policy61351entries/2252820057bytes, infinity. Solver21MiB,
  host1.4GiB used/29available,disk58%/124GiB free. Account32%, no reset credits.
  No full verifier, finite K, global gas allowance or overall go earned.
- Next dictionary placement/lookup correctness and mutations preserving the
  physical table/ownership invariant, then20/52/60-byte helpers, protected gas
  cells and storage/state-debt coupling. Continue original/radix refinement,
  joint table/Q/heap budget and whole source/compiler/target certificate.

Linear-table dictionary/placement checkpoint (2026-10-17):
- Placement cyclic distance and first-match probe search; no-gap placement
  invariant says all earlier slots from a stored key's home are occupied.
  Under placement and bidirectional dictionary representation, lookup equals
  the dictionary for every query. Hash is arbitrary; no distribution premise.
- PlacementUpdate safe slot overwrite preserves occupancy/no gaps, key
  uniqueness and functional dictionary update under explicit chosen-slot,
  old-key exclusion and occupied-path premises. Empty invariants and overwrite
  =lastValue append checked. PlacementBuild fixed-capacity insertion trace
  yields last-record-wins lookup and abstract agreement with radix build;
  construction history covers all occupied slots with at most input.length
  indices, even with duplicates, without assuming actual HT_ORDER contents.
- FindModel32 physical used-byte/stored-key views identify the actual comparator
  chain's answer with model probe search. Under placement/dictionary relation,
  actual chain absence iff dictionary query absent. It does not yet include
  value-cell loads, full find/get semantic lifting or mutator representation.
- Successful mutable-placement-build-v1.log488targets,3.04s,max child
  RSS1190876KiB; mutable-find-model32-v1.log1120targets,4.52s,max RSS1900524KiB.
  Printed main facts use only permitted axioms. Failed drafts fixed reserved
  `at` identifier, if-True normalization and occurrence-directed unfolding of
  lastValue on both sides. Failed logs not evidence.
- Index4490/7322; policy61355entries/2252845514bytes, infinity. Account32%,
  no reset credits. No finite K/full verifier/overall go.
- Next lift chain presence/dictionary values through complete original find/
  get; actual no-growth32-byte set/raw insertion and initial empty-table model.
  nodedb_build preallocates cap>=2*N+2, so original immutable-map refinement can
  use a fixed-capacity trace and avoid growth/deletion there. Mutable runtime
  maps, their growth/deletion/rollback/ownership, global gas/state/table/Q/heap,
  and compiler/target certificate remain separate open work.

Original dictionary find/get/witness lookup checkpoint (2026-10-17):
- FindSlotSpec32 combines physical comparator-chain answers with placement and
  dictionary semantics. FindLift32 composes actual header/hash/index setup.
  FindDictionary32/Call32 give the complete fixed original find body and real
  caller with exact absent sentinel or matching slot and dictionary value.
- HeaderData separates physical header contents from caller local names.
  PureValueCall extends actual pure-call composition to tuple returns.
  GetTail32 executes the real sentinel/value-cell branch. GetDictionary32 and
  GetCall32 compose original find and exact two-word get, at every alignment.
- NodeDbTail32 executes actual missing/present branches and two record loads.
  NodeDbDictionary32 composes real get with original witness lookup, returning
  dictionary record's represented pointer/length or three zero words. Body
  bound<=6*order.length+3 Pan clocks, pure memory/control. All physical header,
  used/key/value/record cells, placement, representation, covering-list/room,
  pointer ranges, actual code and clock premises remain explicit. No hash,
  comparator or inner get execution is supplied as a premise.
- Success mutable-get-call32-v1.log then mutable-nodedb-dictionary32-v1.log
  1132targets; main facts only permitted axioms. Index4501modules/7337facts;
  incremental policy61366entries/2252890183bytes. Claim infinity. Host1.5GiB
  used/29available, disk58%/124GiBfree; account33%, reset credits0.
- Overall progress estimate given to user: roughly35%, range25-45%, based on
  remaining obligations rather than file counts. No whole-program acceptance,
  finite certificate or full verification. Difficult global gas/state/heap/Q
  and compiler/target links remain. Continue actual immutable no-growth table
  construction and mutators preserving the lookup premises; then whole
  original/radix refinement and resource/certificate integration.

Actual original initialization/insertion-components checkpoint (2026-10-17):
- ByteStore proves exact little-endian byte-write projection for the written
  byte and all other residues of the same word, including mapped load result;
  ByteStoreExec proves the actual storeByte state change.
- ZeroWords proves actual memzero word readback through 32-byte and 8-byte
  passes. ZeroBytes proves readback for both repeated byte stores and aligned
  word clears. TableEmpty proves final constructor header writes preserve all
  zero used bytes, actual mapped zero loads, and empty physical KeyModel32.
  TableEmptyHeader supplies actual find/get header and zero count from the
  complete original constructor. Ready/layout/domain/little-endian/capacity
  shape premises are explicit; earlier actual constructor execution is reused.
- InsertProgram/SetProgram identify complete fixed ASTs. InsertScan executes
  raw scan with exact one clock per occupied slot and all-other-local/nonlocal
  frames. InsertScanBound derives empty slot and occupied placement path from
  physical key/used representation and count-bounded covering history. No
  successful scan is a premise. Setter no_growth checks the literal unsigned
  guard from count<=N,cap>=2*N+2,cap<2^64.
- InsertCount/Stores check exact post-memcpy value, used-byte, order,
  order-position and count stores, count declaration/return/scoping, and full
  memory formula under mapped-cell/header-separation premises. SetUpdate
  checks existing-key setter branch's single store and early return. ValueModel32
  checks actual value-word overwrite updates values and preserves keys/used
  under explicit physical ownership/separation, with no-wrap address separation.
- Final closure mutable-empty-insert-closure-v1.log1162targets, printed facts
  only permitted axioms. Index4515modules/7365facts. Incremental policy61380
  entries/2252944184bytes. Claim infinity; no full verifier/global go/finite K.
  Host1.4GiB used/29available,disk58%/124GiB free,account33%,reset credits0.
- Failed drafts fixed explicit UInt8 read projection after branch reduction,
  mod-residue bounds before generalize, explicit ih memory arguments, ofNat0
  simp name, missing FindHeader import/Option.map_none AST normalization,
  actual >+ comparison is reversed .lower, word-zero literal vs OfNat mismatch
  in while guard, qualified QueryBranch.bind, arbitrary MlString BEq lookup,
  Nat multiplication before BitVec cast unfolding, explicit probe slot indices
  in rewriting, and final memory record definitional reduction. Failed logs
  are not evidence; committed final sources have no proof holes.
- Next compose complete actual raw insertion header/hash/scan/copy/suffix and
  prove its final memory preserves table representation and count<=processed.
  Then complete no-growth setter/build trace, last-record-wins original/radix
  agreement and real immutable-map caller refinement. Runtime other key sizes,
  growth/deletion/rollback/ownership, full gas/state/Q/heap and compiler/target
  certificate are still open. Continue autonomously after this checkpoint.

Original insertion copy/representation/layout checkpoint (2026-10-17):
- InsertCopy32 actual aligned32-byte memcpy ABI/body/call (two clocks) and
  post-copy suffix composition. InsertTail32 executes complete real copy,
  value/used/order/position/count stores and return with exact final memory.
- InsertHeader proves generic prefix append, seven actual raw-insert header
  reads/scopes and prepared locals. InsertLift32 actual byte-hash body/caller,
  index declaration and all scopes lift a checked afterIndex suffix to full
  original insertion. The scan and actual tail are separately checked; their
  full body composition still needs explicit physical premises transported.
- MemoryFrame real word/byte writes preserve unrelated mapped byte loads,
  key views, KeyModel and ValueModel. InsertKeyModel32 actual copy installs
  the selected key; actual used-byte store activates only its slot even when
  flags share a word. InsertRepresentation32/ValueModel32 prove full final
  memory represents logical slot overwrite for keys/used/values. Incremented
  count readback unconditional as final store. InsertFrame32 complete outside
  memory frame and physical find/get header preservation under cell separation.
- Layout32 explicitly models all six original allocations, including used,
  with concrete Plan base/size, no-wrap numbers, disjointness, word alignment
  and exact byte-aligned cells. LayoutAddress32 exact scaled Pan addresses and
  distinct key-slot word regions. LayoutWrites32 derives copy/metadata address
  lists and separation. LayoutData32 supplies ordinary-domain mapping/ranges,
  including cap4 used word. LayoutRepresentation32 discharges every copy,
  value, used-byte and metadata separation premise for complete key/used and
  value representation from actual Ready layout/domain and index/count<cap.
  Aligned source hash bytes/words/little-endian remain explicit, supplied by
  checked digest helpers when actual build loop is connected.
- Success mutable-layout-representation-v1.log1171targets; only permitted
  printed axioms. Index4529/7397. Incremental policy61394entries/2253003195bytes,
  infinity. Account34%, no reset credits, host1.4GiB used/29available,disk58%.
  No finite K, full verifier or global spending go. No global estimate bump.
- Failed drafts fixed comparison_arguments's required keyLength argument,
  match-result normalization by cases/simp (identically printed matches may
  not be definitionally equal), qualified usedByte before rewriting raw load,
  append_executes IH needs back proof, nested address rewrite before inner
  normalization, and reducing Plan-dependent header size before decide. One
  dependent build was launched after discovering its prerequisite failed;
  it failed harmlessly and final closure rebuilt checked final sources.
- Next specialize insertion header preservation and real tail to Ready layout;
  compose actual full raw body/scan/tail, no-growth setter and processed-count
  invariant, then original nodedb_build trace and original/radix caller relation.
  Mutable other keys/growth/delete/rollback, protected gas/state ledger, Q/heap,
  whole compiler/target finite certificate all remain open. Continue work.

Complete original immutable-table insertion/setter checkpoint (2026-10-17):
- LayoutHeader32 initializes and preserves all eight fixed header fields and
  the natural count. LayoutTail32 discharges every mapping/separation/copy-mask
  premise of complete real insertion tail from Ready/domain and a separate
  aligned digest buffer before the table. ModelFrame32 transports physical
  table/header/value/word views through memory/control-preserving stages.
- InsertPreparedData checks preserved t/value and actual order/position locals.
  LayoutInsert32 composes complete original htab_insert_raw header/hash/index,
  actual derived first-empty scan, copy/stores/return/scopes. Pays<=covering
  history.length+3 clocks and supplies actual empty slot and occupied path.
- BuildInvariant32 ties actual header, key/used/value arrays and count bound to
  Placement.Builds history. Actual constructor initializes it. Complete actual
  raw insert extends it on absent keys, with count+1<=processed+1. No assumed
  mutator execution or physical array-separation premise remains at this layer;
  Ready/domain/aligned digest bytes/words/before-table/code/clocks explicit.
- MemoryValueCall and TableCallEnvironment check real memory-changing ignored/
  declared calls and three-word mutator ABI. InsertBuildCall32 complete real
  raw-insert caller restores locals and extends invariant with <=processed+4
  clocks. LayoutUpdate32 real duplicate-value update preserves keys/used/header/
  count and extends overwrite history. LayoutSetAbsent32 actual unsigned growth
  guard false, actual raw call and return extend invariant for a new key.
- LayoutSet32 actual original find/call and both setter branches, full scopes,
  count stays or increments, final memory exact update or raw-insert formula.
  Body<=7*processed+6, LayoutSetCall32 actual ignored-result caller+1, restores
  caller locals and extends build history for duplicates/new keys. These are
  Pan/source clocks, not a target price. LayoutEarlier32 proves both complete
  insertion and value update leave every earlier word below the table intact.
- Final mutable-original-set-closure-v1.log1192targets successful, only allowed
  printed axioms. Index4543/7420. Policy61408entries/2253072285bytes, infinity.
  Host1.4GiB used/29available,disk58%/124GiB free,account35%,reset credits0.
  No finite K/full verifier/overall go; overall rough progress estimate stays35%.
- Failed drafts fixed header base opacity via header_cell, memory/shape caller
  argument order, source-clock nonzero proof, missing PanLang namespace, line
  indentation inside record-field applications, beta reduction before lastValue
  rewrite, explicit p.key numeric pointer range, opaque Set.insertCall before
  sequencing, and let/projection record reflexivity after composition. An
  initial_built theorem was added while a local build of that same module was
  finishing; its final current contents were rebuilt in successful v3 and final
  closure before indexing. Failed logs are not evidence.
- Next actual original nodedb_build record loop, keccak calls and earlier-memory
  record/payload frames, capacity/table call initialization, then original/
  radix whole function/caller refinement. Reuse checked candidate capacity
  loop, TableNew call, constructor hash arguments/digest/call libraries where
  literal subtrees agree. Actual branch/store/growth/delete/runtime other keys,
  global gas/state/Q/heap and compiler/target finite certificate remain open.
  Continue original task, no checkpoint stop.

Actual original witness-builder iteration checkpoint (2026-10-17):
- BuildHashFrame32 transports the full physical/logical Built invariant across
  arbitrary changes below the private table. Actual Keccak protected-memory
  theorem supplies that frame from buffer ranges preceding the table, while
  preserving domain/endianness through hashControl.
- WitnessBuildProgram identifies exact fixed original nodedb_build AST, sharing
  checked candidate capacity/hash-argument fragments where literal ASTs agree.
  Original record body is real keccak call then htab_set then ordinal increment.
  Real setter arguments read t, mpt_hash_scratch and actual arr+i*16 record.
- WitnessBuildSetStep invokes complete checked original setter caller, extends
  logical history, increments ordinal, preserves records/input below table and
  every other local/nonlocal control/FFI field; <=7*i+7 clocks after hash.
- WitnessBuildRecords concrete record addresses, ordinary-domain mapping and
  pointer/length load arguments; source record cells remain intact under actual
  hash buffers before records and setter stores above records.
- WitnessBuildRecordStep complete real Keccak caller/body and both setter
  branches. Observes actual four output words/32 bytes, inserts exactly that
  observed key/record pointer, preserves table/records, advances actual ordinal.
  Clock allowance Keccak256.price(length)+7*i+8; hashControl preserved while
  actual Keccak event append remains. No successful hash/set execution premise.
  Ready, actual record words, buffer arenas/before-records, code/domain and
  sufficient clocks remain explicit. Digest is from actual execution; no
  cryptographic injectivity/distribution assumption. Equality of digest/event
  observations between original and radix whole executions remains unproved.
- Success mutable-witness-record-step-v1.log1322targets, only allowed axioms.
  Index4548/7429; policy61413entries/2253099215bytes, infinity. Account35%, no
  reset credits; host/disk remain well within limits. No finite K/full verifier.
- Failed draft normalized length-load associativity in hypotheses before eval
  simplification. Final current sources passed before evidence indexing.
- Next context/code transport through hashControl, history/record references
  and complete original while-loop induction, then capacity/table-call setup
  and whole nodedb_build/caller relation. Existing candidate HashContext and
  record_loop are useful templates; original Locals has t/slice_arr/n/i only.
  Payload/digest noninterference across original/radix private-table memories,
  whole global gas/state/Q/heap and compiler/target certificate remain open.

Complete original witness-record loop checkpoint (2026-10-17):
- WitnessBuildContext transports actual code/globals/domain/hash environment
  through hashControl, while retaining buffer/length bounds. Record source
  allowance monotone in both byte length and ordinal.
- WitnessBuildHistory tracks actual observed digest/record pairs in ordinal
  order. No unique-hash assumption; every history value points to a real input
  slice record. Length bounded by plan.count.
- WitnessBuildLoop whole original record while loop from index+remaining=N,
  Built/input.length=index, real Locals/Records and concrete hash/context facts.
  Actual per-iteration hash/set/increment theorem supplies execution; induction
  preserves final Built/History, produces exactly N pairs, preserves record
  words/all non-i locals, actual hashControl and source-clock upper/lower frame.
  Allowance (Keccak256.price(maximum)+7*N+9)*remaining; this is an intentionally
  loose original source termination allowance, not target pricing/global K.
- Success mutable-witness-loop-v2.log1325targets, allowed axioms. Index4551/7434.
  Failed first loop draft fixed while truth-word iota normalization followed by
  explicit typed-zero if rewrite, before actual body run/fixClock composition.
- Policy61416entries/2253110396bytes, infinity.
  Account35%, no reset credits. No finite K/full verifier/whole-program go.
- Next original allocation/capacity/table-call preparation and loop/return
  scopes, then actual constructor caller. Candidate ConstructorPlan/Prepare/
  PreparedContext/Execution are templates; original prepared state only binds
  i after TableNew.callState, whereas candidate also binds keys/vals/order.
  Their nonlocal fields (memory, globals, domain, codes, endian, clock) coincide.
  TableEmpty.initial_built can transport from TableNew.enteredState to original
  prepared state despite the extra call clock. Reuse candidate prepared_environment
  and prepared_global_other for heap-cursor-only global update.
- Capacity.bounded loses the explicit power exponent; use Capacity.iterate
  count 2 30 to retain finalExp in [2,32], sufficient2N+2 and cap<=4N+4, then
  Capacity.power_shape. Original WitnessBuildProgram.body_shape shares literal
  Constructor.capacityLoop. Whole original price can be
  (Keccak256.price(max)+7*N+9)*N+4*N+46 from cap price bound plus30 clocks.
- Also connect Built+History+Records to actual NodeDb.dictionary32_lookup at
  every query alignment: reparameterize physical Header/KeyModel query pointer;
  define recordSlices pointer=slices((pointer.toNat-plan.records)/16), prove
  record address roundtrip; lastValue some implies input membership, History
  supplies valid record ordinal and mapped cells. lastValue-map-values lemma
  identifies last slice. These are needed before original/radix whole-map API.
- Original/radix real digest and event equality across different private map
  contents is still open: hashing only reads/writes public buffers/input, but
  the existing hash theorem chooses observed actual digest, so cannot simply
  assert the two observed digest sequences equal. Need hash noninterference/
  determinism across private-table memory relation (actual fixed oracle is
  deterministic and checked). All global gas/state/Q/heap/compiler/target work
  remains. Continue autonomously after this checkpoint.

Entire actual original witness constructor checkpoint (2026-10-17):
- WitnessBuildPrepare real htab_new caller/zero-i declaration, both exact
  lexical restoration scopes, initialized Built/Locals/Records and source
  clock. Nonlocal fields equal already-checked candidate prepared state;
  reuse its heap-cursor-only global and hash-environment preservation.
- WitnessBuildPopulate complete allocation/clearing, original record while,
  actual table return and scopes, final Built/History of lengthN and Records.
- WitnessBuildCapacity original cap4 declaration/doubling loop retains final
  exponent bits in[2,32], sufficient cap>=2N+2,cap<=4N+4, real continuation,
  cap local and<=30 clocks. Uses actual checked Capacity.iterate; no capacity
  execution supplied as a premise.
- WitnessBuildExecution entire fixed original nodedb_build AST, capacity,
  allocation plan and actual loop/return/scopes. Final table represents all
  observed actual digest/record pairs with last-record-wins semantics. Exact
  heap cursor/hashControl update to table+72+57*cap+padding. Explicit decoded
  records, source ABI/code/globals, arena/buffer ownership and clock premises.
  Original source allowance (Keccak256.price(max)+7*N+9)*N+4*N+46 is quadratic
  and only demonstrates a conditional source execution; it is not target K.
- Success mutable-witness-execution-v2.log1360targets, only allowed axioms.
  Index4555/7440; policy61420entries/2253133058bytes, claim infinity. Account36%,
  reset credits0, host1.4GiB used/29available,disk58%/124GiB free. No full verifier.
- Failed drafts fixed unnecessary rfl after closed rewriting, reserved scoped
  name, explicit initial-clock projection before omega, and hashControl applied
  to emptyLocals/clock frame using checked hashControl_empty/hashControl_clock.
- Next connect Built+History+Records to complete original NodeDb lookup for
  every query pointer; source constructor caller/environment then original/
  radix actual hash digest/event noninterference and whole context refinement.
  The constructor's observed digest sequence has not yet been identified with
  the candidate sequence under different private table memory contents.
  Global gas/state/Q/heap, startup/ROM/compiler/target and finite certificate
  remain open. Do not stop after this checkpoint; continue original task.

Original constructor-history-to-lookup checkpoint (2026-10-17):
- DictionaryData generic lastValue membership and map-values commute proofs.
- WitnessDictionaryRecords inverts real arr+16*i pointer to slice ordinal;
  constructor History supplies valid input-record membership for every last
  dictionary value, actual ordinary-domain mapping and pointer/length words.
- WitnessDictionaryLookup directly connects Built/History/Records to complete
  actual original nodedb_lookup for every query pointer/alignment. Rebuilds
  query-independent physical header/KeyModel with the new query pointer,
  derives placement/lastValue representation/covering history and real value/
  record cells. Returns QueryExecution.valueOf(lastValue query(sliceEntries))
  with <=6*input.length+3 source clocks and pure memory/control. Exact same
  tuple format as radix API; no cryptographic uniqueness assumption.
- Success mutable-witness-dictionary-lookup-v2.log1331targets, permitted axioms;
  index4558/7446, policy61423entries/2253142829bytes, infinity. Account36%, no
  reset credits. No finite K/full verifier/whole-context correctness.
- Failed draft explicitly unfolded ValueModel32 when instantiating raw value
  cell predicate; all current sources passed before indexing.
- Next highest-value map gap is actual Keccak digest/event congruence across
  original/radix states with different private table memory/code. Existing
  hash proofs yield observed digests and frames, not cross-program equality.
  Required helper code is identical and fixed, but full source.code maps differ
  at nodedb_build/lookup, so do not assume whole-code equality. Prove a memory
  relation on public state/input/pad/output buffers and required code entries.
- Useful inspected APIs: Keccak.post source stp bytes writes answer bytes and
  nextFfi appends actual keccakf IO event zipped input/output. Keccak.f1600_execute
  accepts actual readBytearrayWordHOL result. Existing Keccak.call_execute /
  f1600_mapped hide readArray behind an existential; strengthen locally by using
  ByteArray.read200 and actual f1600_execute to retain the readArray fact.
  KeccakAbsorb.prepared=stateLanes(bind source i0) stp(isUnaligned blk)0 17;
  lanePost uses memory(stp+i) XOR inputValue(source inputWord). inputWord is
  either aligned load or eight expanded LE byte reads, with blk/i locals.
  stateLanes memory/FFI normalization can support buffer congruence.
- Complete original constructor/caller and lookup/caller environments can use
  CodeEnvironment.finite_lookup. Candidate ConstructorEnvironment has the same
  two formals slice_arr/n; copy its raw lookup but use actual original body.
  Declared constructor caller must use Input.CallNormal.return_execute because
  globals heap_ptr and FFI events change; pure/memory-only call helper does not
  apply. Candidate Constructor.call_execute is an ignored-result template.
- Remaining global input/gas/state/Q/heap and compiler/target finite certificate
  work remains; claim stays infinity. Continue original task autonomously.

Keccak public-buffer/event agreement checkpoint (2026-10-17):
- ByteArrayAgreement: exact byte-array read congruence on requested bytes,
  word8 byte-read congruence on aligned cells, and arbitrary-region agreement
  preserved by identical tail-first byte-array writes, including failed-store
  fallback. No full-memory/code/global/local/clock equality required.
- KeccakAgreement retains the actual readArray through real permutation ABI,
  pairs two actual calls from state-buffer cell agreement, and proves exact
  post-memory region/FFI agreement using fixed sourceOracle. Unrelated code
  and private memory may differ.
- KeccakAbsorbAgreement/LanesAgreement: actual aligned load and eight expanded
  LE byte loads agree from their real read cells. XOR lane writes and all17
  real stateLanes preserve arbitrary-region agreement containing those reads.
  Includes arbitrary alignments, no cryptographic uniqueness assumption.
- KeccakAbsorbRead strengthens complete body execution with explicit actual
  prepared-state input bytes. KeccakAbsorbPaired/PairedCall combine common
  actual input bytes with real permutation, scope/return and caller ABI.
  Public memory and observable FFI events agree. Caller locals restored;
  each actual block call costs exactly19 source clocks.
- Keccak256PairedBlock/PairedLoop: actual full-block body/index increment and
  arbitrary full-block while preserve chosen public memory and FFI agreement.
  Per-run own hashControl/clock/locals/outside-state frames;20clocks/block.
  Required helper code entries explicit; full source.code equality NOT assumed.
- Successful logs bytearray-agreement-v3.log594targets,keccak-agreement-v3.log
  679,keccak-absorb-read-v2.log678,keccak-absorb-paired-v4.log682,
  keccak-absorb-paired-call-v2.log685,keccak256-paired-block-v1.log697,
  keccak256-paired-loop-v1.log699. All final transitive axioms allowed.
  Index4567modules/7468printed facts. Policy61432entries/2253201027bytes,
  infinity; no isolated full verification or finite K. Account37%,0credits.
- Failed draft logs are NOT evidence: fixed numeral1 versus1#64 instances
  in raw recursive array definitions, dependent decidable-domain rewrites by
  pointwise byte-reader equality, beta/association normalization of read facts,
  and excessive defeq unfolding of target memory. Explicit projection theorem
  with simp-only scopes and local maxHeartbeats1M makes two-target ABI proof
  check. A mixed failed log was rejected by index script before writes;
  only successful logs above were subsequently indexed.
- Next: deterministic memcpy/memzero/padding/output memory congruence, then
  complete paired keccak256 body/caller so original/radix observed digests and
  events can be identified. Full map/context/compiler/target/global resource
  bounds and finite certificate remain open. Continue; do not stop here.

Complete paired Keccak256 checkpoint (2026-10-17):
- MemoryRegionAgreement arbitrary-region equality preserved by identical
  ordinary word/byte stores and store lists. CopyRegionAgreement exact byte/
  word memoryMany and memoryWalk preserve equality on regions containing read
  cells, including overlapping sequential copies. CopyGeneralRegionAgreement
  composes both aligned word prefix and byte suffix into exact resultMemory.
- ZeroRegionAgreement exact memory32/memoryWord/finalMemory preserves region
  equality. Keccak256PaddingAgreement combines actual zeroPadState, actual
  memcpy callState, first marker byte and read/OR/store final bit. Exact
  paddingPrefixState memory/FFI agreement; no assumed copy/hash oracle.
- Keccak256OutputAgreement canonical outputState with actual execution of both
  output paths, source-clock/locals/hashControl/FFI/outside-output frames and
  region memory agreement. PairedPadding composes entire final-block actual
  zero/copy/stores/absorb/output/return, preserving public memory/events, own
  source clock bounds and outside buffers. PairedAfter adds rem scope.
- Keccak256Composition actual clearing and stp/i declarations/scopes compose
  supplied actual block/tail executions. PairedExecution entire fixed body,
  own price202+20*(length/136), event/public memory agreement, outside-buffers
  frames. PairedCall real ABI restores each caller's locals, price+1.
- Keccak256BufferAgreement BufferRegion contains raw/aligned cells in state200,
  inputlength,pad136,output32 buffers; all actual block/tail read-region facts
  derived by address algebra, no full-code or full-memory equality. Actual
  paired calls return identical MemoryBytes.wordsOf output and complete FFI
  state/event history, plus restored locals and region agreement.
- Latest successful keccak256-buffer-agreement-v2.log723targets includes all
  twelve new modules and their closures; only permitted axioms. Underlying
  successes memory-region-agreement-v1.log619,copy-region-agreement-v1.log639,
  copy-general-region-agreement-v1.log640,zero-region-agreement-v1.log625,
  keccak256-padding-agreement-v1.log701,keccak256-output-agreement-v2.log697,
  keccak256-paired-padding-v1.log712,keccak256-paired-after-v1.log714,
  keccak256-composition-v3.log701,keccak256-paired-execution-v2.log720,
  keccak256-paired-call-v1.log722. Index4579/7506,policy61444/2253269038bytes.
  Account37%,0credits; claim infinity; no full verifier or finite K.
- Failed drafts fixed truth-word0 instance reduction with full simp on output
  alignment, multiline let application parentheses and final explicit rfl for
  opaque hashingExit, explicit loop-clock projections before omega and digest
  memory-address aliases with congrArg. Failed logs never indexed.
- NEXT: joint original/radix constructor record and loop relation using paired
  hash actual runs and equal digests. EntryData comes from allocated_entry,
  both Keccak.Environment values and common Buffers; ordinary domains agree,
  both little-endian, helper code same, globals heap_ptr may differ.
- Existing record_step proofs hide hashed states and observed keys. Extract
  local strengthened record/after-hash lemmas accepting actual paired hash
  runs. MutableTable.WitnessBuild.after_hash_step target is bind(post memory,
  clock-paid)i(index+1); its proof has exact pure-memory updates, but theorem
  only states hashControl (erases events). Need strengthen separate new lemma
  to retain actual FFI equality or CopyContext.control and earlier-memory
  frame. Candidate Constructor.after_hash_step already states control=control
  source (retains FFI), but hides equality target=suffixState; strengthen new
  lemma with canonical target/frame for arbitrary public region below pools.
- Region for joint loop should include decoded input and hash buffers while
  excluding both current private tables. q<min(tableStarts) alone fails when
  old private tables lie below later allocations unless relation excludes old
  private tables too. Use explicit BufferRegion/read-only input ownership;
  existing Context.before only places state/pad/output before records, NOT
  every slice input. Real decoder input slice bounds/nonalias reachability
  still need proof. No whole-map/context equivalence established yet.
- All global gas/state/Q/heap/compiler/target/finite certificate work remains;
  continue autonomously after checkpoint, not a stop point.

Actual joint record loops and lookup agreement checkpoint (2026-10-17):
- MutableTable.WitnessBuildSetFfi strengthens original after-hash setter suffix
  with actual target.ffi=source.ffi, earlier memory frame. RecordHash accepts
  supplied actual hash-call run, actual clock/local/control/Protected frame,
  then proves full literal original recordBody; retains key=WordKeys.key of
  actual hashed scratch, target FFI equality to hashed state and all q<T frame.
- WitnessRadix.ConstructorStepExact retains target=suffixState from actual
  after-hash copy/stores. ConstructorRecordHash accepts actual hash run and
  retains concrete digest/canonical suffix state/FFI. ConstructorPublicFrame
  proves arbitrary earlier query words unaffected by all six real writes,
  using exact write_cells footprint, write_bounds and no-wrap.
- WitnessBuildRadixStep.paired_record_step derives both actual hash argument
  reads from own Records/FixedData, actual paired allocated Keccak call, equal
  digest words/key and both complete recordBody executions. Advances original
  Built/Records and candidate Prefix/FixedData/Mapped/Locals with common key,
  each own clock/control bounds, equal FFI and public memory. Existing Context
  and HashContext bundle required helper code and buffer/arena facts. No full
  code/global/private memory equality required; current buffers and chosen
  public region precede current table/private write pools explicitly.
- WitnessBuildKeyHistory keyRecords=range-map(keyFor(ofNat i),real recordAddr i),
  KeysMatch exact original-history equality; empty and snoc preserve it using
  actual setKey_earlier and setKey_current (including duplicate digests).
- WitnessBuildRadixLoop.paired_record_loop complete actual original and radix
  record whiles from same N and explicit contexts/arenas/public ownership.
  Final original Built/History/Records, candidate Prefix/FixedData/Mapped,
  KeysMatch full observed histories, equal FFI/public memory, own source clock
  bounds/non-index locals/control. Induction calls actual paired record_step;
  no per-record run or crypto oracle assumed.
- WitnessBuildDictionaryAgreement decodes real history record addresses and
  proves sliceEntries equals OrdinalTree.entries keyFor sliceFor(ordinals N).
  WitnessLookupAgreement.paired_dictionary_lookup complete actual bodies both
  return identical last matching slice tuple for every query alignment. Uses
  original Built/History/Records/KeysMatch plus actual radix QueryMemory.Represents,
  root cells and code/ABI/byte-view/clock premises; both preserve memory/FFI.
  Original<=6*N+3, candidate<=262 Pan clocks, never target certificate prices.
- Success constructor-hash-steps-v1.log1325,constructor-record-hash-frame-v1.log
  859,mutable-witness-radix-step-v2.log1350,mutable-witness-key-history-v2.log
  1317,mutable-witness-radix-loop-v1.log1354,mutable-witness-dictionary-agreement-v2.log
  1343,mutable-witness-lookup-agreement-v1.log1345; all allowed axioms.
  Index4589/7518,policy61454/2253325560bytes. Account37%,0reset credits;
  host1.5GiBused/29available,disk58%/123GiBfree. Infinity,no full verifier.
- Failed drafts: avoid reserved `public` binder; use inRegion. Importing old
  record modules means do not redeclare recordPrice. Refer ordinals with open
  WitnessRadix.BackingLayout and set local Classical.propDecidable for function
  keys in theorem statements. Rewrite prior KeysMatch only on lhs via calc:
  unrestricted rw changes input.length inside rhs and breaks map matching.
- NEXT allocation and finish connection. Actual two constructors allocate same
  pool extent/capacity, so heap_ptr can remain equal across replacement. Their
  current private table bytes differ after construction. Old private tables
  below later T mean global equality q<T is too strong; region must exclude
  old private tables while including buffers/other public allocations.
- Candidate Constructor.finish calls helper_built and yields actual tree from
  synchronized Prefix. Its existing control retains FFI, but no outside-private
  memory frame is exported. Need strengthen actual helper/public footprint,
  then lift paired records + finish + table return/scopes/initial allocation.
  Actual decoder read-only input slice bounds must establish BufferRegion
  agreement and nonalias premises (Context.before only state/pad/out<R).
- Inspected helper pipeline: HelperCall→HelperBuilt→HelperExecution→HelperCore→
  LoopTermination. LoopResult records execution/representation/control/clocks
  but no memory frame. LoopTermination has four canonical cases: terminal
  finish leafPost, terminal resume resumePost, uniform unaryPost, split
  SplitCount.post. Add public-frame lemmas on these exact transforms and
  strengthen a parallel loop/helper result without modifying fixed imports.
  Unary probably only locals/clock; leaf stores context.dest; split scatter/
  copy/branch/pending writes into private pools. Full Invariant.atLayout
  supplies exact addresses/pool bounds. Existing old proof library untouched.
- Main obligation still incomplete: joint full constructors/callers, map lifetime/
  ownership and whole-context refinement, runtime mutable maps20/52/60 bytes,
  global gas/state/Q/heap potential, source/compiler/startup/target finite K.
  Do not stop after this checkpoint; continue original task autonomously.

Whole paired witness constructor checkpoint (2026-10-17):
- HelperPublicFootprint PublicWord excludes precisely WriteOffset cells, so
  immutable input-record/key words can remain public. Exact leaf/resume/unary/
  split transforms preserve it; split uses existing post_away, row_cell,
  ContextAt, allocation_writable, invariant branch/stack room. New parallel
  HelperLoopPublicFrame strong agenda induction proves actual mainLoop's
  evaluated target memory frame, without changing existing fixed proofs.
- HelperCorePublic/NonemptyPublic/EmptyPublic/BuiltPublic lift the frame through
  zero tests, prefix declarations/restores and both sizes. HelperCallPublic
  actual ABI, ConstructorFinishPublic actual helper+table-return retain frame.
- MutableTable.WitnessBuildRadixFinish pairs original return with full radix
  finish; original Built survives emptyLocals, actual final QueryMemory tree,
  public memory and FFI agreement. AllocatedPublicFrame derives PublicWord and
  constructor suffix write separation uniformly from q.toNat<table for actual
  allocationPlan, excluding records from mutable cells.
- WitnessBuildPreparedAgreement actual allocation initialization state memory
  preserves selected public region and FFI; common globals/heap updated equally.
  Earlier private tables may differ outside region. Both prepared clocks exact.
- WitnessBuildRadixPopulate full paired record loops, radix helper, both returns
  from actual entered invariants; final common History/KeysMatch and actual
  original/radix representations, FFI/public memory and own source allowances.
- WitnessBuildRadixTable both actual htab_new allocation/zeroing callers, array
  setup, whole paired population and every scope. Raw source records plus
  public record-cell equality derive real candidate decoded record facts.
  Preserves global equality, FFI/public memory, own source clock bounds.
- CapacityExact retains finalExp=initialExp+paid and strict upper cap<4*N+4 or
  no growth from initial exponent. CapacityExactEntry generic cap declaration
  around arbitrary continuation. CapacityPairedEntry proves unique sufficient
  exponent from strict bound (initial4 exception), hence same paid and common
  resulting locals, plus each actual prefix/continuation run and full frame.
- WitnessBuildRadixExecution.paired_execute entire actual original and candidate
  nodedb_build. Shared actual cap determines allocationPlan ready; both bodies
  allocate/populate/return same table address. Actual final Built/History/
  Records/KeysMatch and radix QueryMemory initialTree refer to same real keys/
  slices; equal globals/heap cursor, complete FFI histories/public region.
  Own exact hashControl to initial source with actual heap update; own source
  wholePrice bounds retained (original quadratic,candidate linear), not target K.
- Context premise is forall capacity:Context source(allocationPlan R T N C)...
  because Context depends only on R/N and source helper/global facts, not C
  or private table state. It does NOT assume ready for all C; only selected
  C=2^bits gets actual allocation_ready. Can later wrap with explicit entry
  code/env/buffer facts like original execute. Input ownership: arbitrary
  selected public region agrees, contains all raw/aligned hash buffers and
  decoded record cells, and lies below current table. Old private tables can
  be excluded, fixing the too-strong all-q<T relation for sequential maps.
- Success radix-helper-public-footprint-v2.log742,radix-helper-loop-public-v1.log
  743,radix-helper-core-public-v2.log746,radix-helper-nonempty-public-v1.log749,
  radix-helper-empty-public-v1.log750,radix-helper-built-public-v1.log751,
  radix-helper-call-public-v1.log779,radix-constructor-finish-public-v1.log780,
  mutable-radix-finish-v1.log1377,mutable-radix-prepared-public-v1.log1342,
  mutable-radix-populate-v2.log1381,mutable-radix-table-v2.log1395,
  radix-capacity-exact-v1.log584,radix-capacity-entry-exact-v2.log587,
  radix-capacity-paired-v2.log589,mutable-radix-execution-v2.log1407.
  Index4606/7543; all printed axioms permitted. Prior incremental policy
  61470entries/2253400378bytes before newest Execution source, latest policy
  run recorded separately. Claim infinity; no full verifier or finite K.
  Account39%,0reset credits; host1.5GiBused/29available,disk58%/123GiBfree.
- Failed drafts fixed row-cell base aliases by explicit change before rw,
  capacity-vs-count bounds via ready.room, local let rewrite with change (rw
  on value is invalid), explicit plan-count/source-price types before omega,
  finite-map ext_lookup requires Flapjack.FiniteMap.MapKeys import, no bare
  lt_trichotomy in lean imports (use by_cases), and avoid subst choosing an
  unintended finalExp=2+paid equality; rewrite selected equalities explicitly.
- NEXT actual constructor ABI. ConstructorEnvironment.environment is fixed to
  candidate body and hides raw locals equality. Generalize locally over body,
  retaining callee.lookup=Constructor.rawLocals, then use ext_lookup to choose
  common callee for source original body and right candidate body. Paired full
  body theorem applies to callEntryState with common locals, memory/globals/
  FFI equal fields and source clocks minus1. Ignored caller can use standard
  evaluateHOLFiniteState_call_return_caller_locals; assigned/scoped caller must
  use Input.CallNormal.return_execute in Input/CallResume.lean (globals/events
  change; memory-only caller lemma is unsuitable).
- After caller contract, establish actual two witness-map initialization call
  premises from decoder/heap reachability and record/input buffer ownership;
  preserve old private maps across second allocation and runtime queries.
  Existing paired_dictionary_lookup handles represented common key history.
- Entire goal STILL incomplete: no whole-context replacement or global gas/
  state/Q/heap/resource/compiler/startup/target bound, runtime mutable maps
 20/52/60bytes unresolved, claim infinity. Continue autonomously; no stop point.


### 2026-10-17 — real witness constructor callers, null empty arrays, decoded geometry

- WitnessBuildEnvironments derives shared finite ABI locals from each actual
  nodedb_build code entry. WitnessBuildRadixCall completes both ignored calls
  and arbitrary decCall continuations with actual returned table pointers,
  caller local restoration and equal globals, FFI/public memory. Whole-program
  caller reachability remains conditional. Successful mutable-radix-call-v1.log
  1410targets, permitted axioms. Source price+1 remains a Pan clock allowance.
- Empty decoder returns array pointer0,count0. General paired constructor
  correctly assumes positive record arena and cannot cover this case.
  ConstructorEmptyPublic executes candidate zero case using an unused ghost
  record arena at table, actual capacity4/allocation/empty helper/return. Adds
  full globals/FFI and every earlier-memory frame. Original WitnessBuildEmpty
  does the actual matching capacity/allocation/zeroing/skip-loop/return, with
  empty physical Built invariant. Neither reads records or hashes.
- WitnessBuildEmptyRadixCall.paired_empty_call handles arbitrary incoming array
  pointer (including0), ignored and scoped returned calls with shared ABI.
  Ready ghost plan, original empty Built and candidate actual empty tree/root,
  equal globals/FFI/public memory, own source allowance43/44 survive callers.
- Input.VarList.RecordGeometry proves real pointer natural address and item
  extent inside encoded input for every index, including zero-length end items;
  Arena and record end+8<=actual array. Does not bound mathematical input.length.
  ConstructorData derives nonempty array positivity/alignment/range, raw pointer
  cells without requiring input byte reads, and each real Keccak input arena.
  Fixed state/pad/output arenas and their startup origins remain premises.
- BufferRegionBelow gives actual raw and aligned accesses in a selected prefix,
  allowing old private tables outside public equality after the first map.
- Successful radix-empty-public-v2.log923,mutable-empty-v1.log1359,
  mutable-empty-radix-call-v2.log1376,input-record-geometry-v1.log1302,
  decoded-constructor-data-v1.log1326targets. Permitted printed axioms only.
  Failed empty-public-v1 needed explicit update-value reduction and untyped
  congrArg intermediate for capFrame projection; failed paired-empty-v1 lacked
  MemoryRegionAgreement import. Failed logs not indexed.
- Host1.4GiBused/29available,disk58%/123GiBfree. Account40%,0resetcredits.
  All checks use resource guard24GiB and one limiter slot, no full verifier.
- NEXT adapt decoded pointer/length cells and buffer/public layout to the actual
  constructor entry; then preserve the first private dictionary while building
  the second and compose both actual run_attempt decCalls. Global/target bound,
  whole-program replacement and finite K remain open. Claim infinity. Continue.


### 2026-10-17 — decoded constructor data and own private-memory frames

- MutableTable.WitnessDecodedData.decoded_constructor_data derives natural
  record-array bounds/alignment, exact word-indexed sliceFor pointer/length
  reads, ordinary hash Buffers and low-prefix BufferRegion plus record-cell
  ownership from actual VarList.Records. Fixed hash arenas, their ordering,
  array end before selected boundary remain explicit reachability premises.
  Successful mutable-decoded-data-v3.log1439targets. v1/v2 failed on let aliases,
  BitVec.ofNat_toNat producing setWidth (simplify setWidth_eq), and byteAddress
  i*16+8 vs nested row+8 (explicit address equality). Failed logs not indexed.
- Input.VarList.RecordsFrame.of_cells/of_before retains actual decoded record
  offset validity after later memory changes, using only two cells per item.
  Successful input-records-frame-v2.log1300; v1 redundant rw on absent plan.count.
- MutableTable.WitnessRunAttempt.initialization_shape checks actual source AST
  suffix after header validation: nested nodedb/codedb constructor calls then
  real runtime. input_arguments/paired_input_arguments derive both actual loads
  from input structure, valid for zero array/count too. Success
  mutable-run-attempt-v3.log1466; v1 rfl insufficient for well-founded progToHOL
  equations and missing valueIsWord/valueWord; v2 hypothesis address aliases
  needed explicit change before simp. Neither failed log indexed.
- Existing paired memory agreement alone was insufficient for sequential maps:
  the first original/radix private dictionaries differ. Added independent own
  memory frames for a selected safe region to actual paired step, full loops,
  full population/helper/returns, allocation/setup/scopes, complete bodies and
  actual ignored/scoped returned callers. Safe requires q<T and disjointness
  from actual Keccak state/pad/output buffers; no assumed execution frame.
  Actual per-hash Protected frames + original setter/candidate six-store frames
  + helper PublicWord + allocation earlier-memory frames compose. Final actual
  body/caller memory at every safe query equals its own initial memory.
- Checked new modules WitnessBuildRadixStepFramed,LoopFramed,PopulateFramed,
  TableFramed,ExecutionFramed,CallFramed. Logs mutable-radix-step-framed-v3.log1350,
  mutable-radix-loop-framed-v1.log1354,populate-framed-v1.log1383,
  table-framed-v2.log1397,execution-framed-v1.log1409,call-framed-v1.log1412.
  Printed axioms permitted. Failed step drafts: Unicode arrow immediately
  before rightTarget parsed RelHom arrow-r notation (always space arrows);
  final exact with proof metavariables must be refine. Failed table draft
  broad textual replacement also changed local finalMemory type; fixed.
- NEXT instantiate safe region from earlier dictionary/record geometry, then
  transport original Built and candidate QueryMemory representation/read
  support through second construction, compose two actual run_attempt calls.
  Existing QueryMemory.reads/represents_of_agreement and BackingLayout
  Located/Protected/located_reads provide support machinery. May need retain
  final completed support from actual helper loop, rather than only the weak
  QueryMemory.Represents result. Existing constructor proofs supply model but
  not explicit final read-support bound. Startup allocation, entire decode/
  headers reachability, whole runtime and global resource/compiler/target
  budget still open. Claim infinity; no final certificate or full verification.
- Account40%,0resetcredits. Host1.4GiBused/29available,disk58%/123GiBfree.
  Continue autonomously, no checkpoint stop.


### 2026-10-17 — completed lookup support and preservation of both earlier dictionaries

- AllocatedReadBounds.cell_bounds/protected_bounds proves all candidate protected
  read cells between actual record arena and final heap cursor. protected_safe_
  for_later derives q<newTable and actual Keccak Protected from fixed arena
  ordering. Success radix-allocated-read-bounds-v2.log777targets. v1 by decide
  could not reduce type containing free plan; explicit change to numeral bound.
- OpenGraphCompletedSupport.completed_supported retains concrete QueryMemory
  reads within closed OpenGraph reads. Closed child slots are real reads.
  InvariantFinishSupported retains that support through actual terminal fill,
  located graph preservation, immutable cells and actual return state.
  LoopSupported/result_next_supported and LoopTerminationSupported propagate
  support through all four actual transitions and decreasing agenda induction.
- HelperCoreSupported,HelperNonemptySupported,HelperBuiltSupported,
  HelperCallSupported,ConstructorFinishSupported retain existing execution,
  model, public memory and own clock/control frames plus all final QueryMemory
  reads in BackingLayout.Protected layout layout.count. Empty support vacuous.
  ReadFootprintStable is needed across changed locals even when memory agrees;
  QueryMemory.reads is not definitionally insensitive to state locals. Failed
  helper caller v1/v2 fixed with explicit reads_stable and correct proof-goal
  metavariable. Failed logs not indexed.
- MutableTable WitnessBuildRadixPopulateSupported uses actual finish_supported
  to retain support, identifying both actual target (determinism) and root
  (same stored root word). TableSupported,ExecutionSupported,CallSupported carry
  it through all actual allocations, bodies and ignored/scoped call ABI, while
  retaining each own earlier-memory safe frame. Checked full caller exports
  physical original Built/History/KeysMatch/Records and concrete radix rep/
  protected read support, equal globals/FFI/public region, independent prices.
- WitnessPriorRadixFrame.prior_radix_preserved uses actual later safe frame,
  allocated bounds and read-support stability to preserve earlier root mapping/
  word, whole represented dictionary and read support. BuildInvariantFrame32
  built_of_cells transports the entire original Built invariant from only its
  allocated cells; used-byte/aligned key views and every header/value handled.
  built_preserved_by_later discharges those cells from actual safe frame and
  old allocation geometry. WitnessPriorRecordsFrame.prior_records_preserved
  preserves actual original record pointer/length cells. This resolves BOTH
  model-level preservation obligations for sequential witness constructors.
- Success logs radix-completed-support-v1.log608,
  radix-terminal-supported-v1.log728,radix-loop-supported-result-v1.log743,
  radix-loop-supported-v1.log750,radix-helper-nonempty-supported-v1.log753,
  radix-helper-built-supported-v1.log757,radix-helper-call-supported-v3.log785,
  radix-constructor-finish-supported-v1.log786,mutable-populate-supported-v1.log
  1394,mutable-table-supported-v1.log1406,mutable-execution-supported-v1.log1418,
  mutable-call-supported-v2.log1423targets. Permitted printed axioms only.
  Failed final batch v1 built_of_cells tried composing header0 equality before
  simplifying table+0; explicit normalized zeroHeader fixed it. Batch v1 also
  built caller successfully but was not indexed; v2 complete success indexed.
- NEXT compose two actual run_attempt constructor decCalls, using complete
  paired supported caller + earlier Built/Records/Query support preservation.
  New table equals first final cursor, both allocations same chosen capacity,
  first private memory differs across programs but has own safe frame. Decode
  si40/48,56/64 reachability and input-array preservation through header decoder/
  validation still needed. Current empty caller has physical empty maps but no
  hashControl/read-support export; empty tree support is trivial and can wrap
  existing proof. Full nonempty caller signature has ∀capacity Context; entry
  code/buffer/global obligations can wrap from actual decoded_constructor_data.
- Remaining entire runtime contextual replacement, gas/state/Q/heap potential,
  compiler/startup/target allowance and finite K still open. No full verifier.
  Claim infinity. Account40%,0resetcredits; RAM1.4GiBused/29available,disk58%.
  Continue autonomously; no final checkpoint stop.


### 2026-10-17 — conditional actual two-map initialization composition

- WitnessBuildNextContext.Context.after_allocation/after_constructor transports
  a second map's complete hash/set context across the first allocation/caller
  hashControl. Uses first allocation separately from second plan; Context does
  not depend on mutable memory, which is carried separately by own frames.
- WitnessDictionaryPair.DictionaryObservation packages chosen bits, distinct
  count, real insertion history/logical table, key history and stored radix root.
  DictionaryPair carries Ready, both physical/logical models, history/KeysMatch,
  actual Records, root and read support. preserved_by_later combines all three
  checked prior-model preservation bridges. Missing ConstructorPlan import in
  v1 caused unknown allocationPlan/initialTree; v2 checked. No failed indexing.
- WitnessDictionaryFields.of_fields transports paired models through actual
  declaration binding/restoring and clocks, using memory/domain/endian equality.
  WitnessCallResult.ConstructorReturn packages actual ignored/scoped ABI;
  .fields derives code/domain/endian/eshapes from actual evaluator invariant.
  ConstructorPairResult retains complete supported caller with independent
  earlier safe frames and own hashControls/clocks. WitnessDictionaryCall gives
  this packaged result from all actual nonempty caller entry premises.
- WitnessInitialization.initialization_execute composes both actual nodedb/codedb
  decCalls, resuming real runtime with precisely both scope restores.
  paired_initialization uses first and second actual ConstructorPairResult,
  old allocation end<=secondTable and hash buffer ordering to preserve first
  original Built/Records and radix represented/support, then binds codedb and
  retains BOTH map models at real runtime entry. Equal caller locals, globals,
  complete FFI and selected public memory hold there. Does not assume a run of
  the whole initialization suffix; derives it from actual constructor contracts.
- Successful mutable-next-context-v1.log1332,mutable-dictionary-pair-v2.log1359,
  mutable-call-result-v2.log1437,mutable-dictionary-call-v1.log1439 (also fields),
  mutable-initialization-v2.log1500targets. Permitted printed axioms only.
  Failed call-result-v1 reserved field scoped renamed resume. Failed init-v1
  rw would not match abstract withTable against concrete setter; simp only
  withTable at second call equation and target before rw fixed it. No failed
  logs indexed.
- NEXT unify null array/count0 and positive decoded arrays under packaged call
  API. Existing paired_empty_call must export its individual earlier-memory
  frames (already proved in body; currently only joint agreement exported).
  Empty map's logical record arena is ghost table,count0, because actual
  record pointer0 is never read. DictionaryObservation may therefore use a
  record base different from actual call argument only when count0. Consider
  general packet of post globals/cursor + oracle equality (code/domain/endian
  obtained from ConstructorReturn.fields) instead of requiring whole hashControl
  for empty API. Source clock allowances +2 uniformly cover empty and nonempty.
  Then derive second entry raw cells/context from first actual own frame and
  decoded_constructor_data, initial +both prices supplies second clocks.
- Conditional composition is now checked but initial concrete call premises,
  decoder/header/startup reachability and whole runtime contextual refinement
  remain open. Global gas/state/Q/heap/compiler/target budget and finite K open.
  Claim infinity, no full verification. Account41%,0resetcredits. Continue.


### 2026-10-17 — uniform empty/nonempty decoded caller and actual capacity/cursor bounds

- WitnessBuildEmptyControl and WitnessRadix.ConstructorEmptyControl add exact
  hashControl to real zero-record bodies: initial source with heap_ptr T+304.
  WitnessBuildEmptyRadixCallControl also exports both individual earlier-memory
  frames plus real ignored/scoped calls, globals/FFI/public equality and models.
  WitnessEmptyDictionaryCall packages this into ConstructorPairResult with
  logical record arena at table,count0, arbitrary actual array argument. Empty
  tree support is false and actual original empty Records vacuous. No hash or
  record access introduced. Arbitrary supplied sliceFor ignored for empty tree.
- WitnessAnyDictionaryCall handles all counts: positive count keeps actual raw
  record address, zero uses ghost table base. Positive-only record lower/before/
  aligned/context premises; unconditional fixed environment/domain/little and
  table/code facts support empty. Initial allowance wholePrice+2 covers empty
  caller conservative 48-clock premise while returned packet retains +1 lower
  clock bounds (actual empty cost<=43/44). Input raw null0 is preserved in ABI.
- WitnessEntryEnvironment separates fixed code/global metadata from decoded
  records/arenas/size geometry. WitnessDecodedDictionaryCall derives ALL real
  constructor memory/context premises from actual VarList.Records, fixed hash
  arenas/order, array end<=public boundary<=table and per-item size bounds.
  Source/candidate selected low-prefix memory agrees; old private maps excluded.
  Both empty and nonempty branches covered. Actual argument eval, initial fixed
  metadata/arenas, caller relation/clock/heap and decoded reachability remain
  explicit. Neither raw record reads nor hash input arenas are assumed.
- WitnessNextEnvironment carries fixed metadata through first cursor update
  and hashControl, including empty. Input.VarList.RecordsSafeFrame.of_safe_frame
  preserves second actual decoded record array through first actual constructor
  safe frame; no positive-array premise for empty. v1 arrayEq rewrote number
  hypotheses but not final goals; v2 aligns aliases before rw. Failed log not
  indexed.
- Found missing exported bound needed for second allocation: selected capBound
  was internal to paired_execute_supported. Retained 2^bits<=4*N+4 through that
  theorem, paired_call_execute_supported and ConstructorPairResult.capacityBound.
  Updated DictionaryCall packing and empty packet cap4 proof. Complete dependent
  API/initialization/decoded callers rebuilt successfully. Earlier successful
  logs for unchanged names superseded by new source-hashed evidence.
- WitnessAllocationBounds .heap_bounds/.heap_words prove exact actual heap_ptr,
  lower/alignment/arena upper and chosen cursor<=T+72+57*(4*N+4)+7. two_map_room
  proves both witness allocations fit arena from B<=134217712, N1+N2<=B/4 and
  T<=2701131776+128*B+1048576. Last two count/cursor premises are not execution
  reachability results; do not promote to unconditional heap/global claim.
- Successful witness-empty-controls-v1.log1370 (two modules),
  witness-empty-caller-control-v1.log1376,witness-empty-dictionary-call-v1.log1441,
  witness-any-dictionary-call-v1.log1443,witness-entry-environment-v1.log1324,
  witness-decoded-dictionary-call-v1.log1542,witness-next-entry-fields-v2.log1426,
  witness-cap-export-body-v1.log1418,witness-cap-export-caller-v1.log1421,
  witness-cap-export-packet-v1.log1437,witness-cap-export-api-v1.log1443,
  witness-cap-export-closures-v1.log1505,witness-cap-export-decoded-v1.log1542.
  All printed axioms permitted. New actual bounds module also in API success.
- NEXT derive both actual decoded constructor invocations at initialization,
  rather than assume two ConstructorPairResults. First call uses decoded
  contract. Carry second VarList.Records via of_safe_frame, EntryEnvironment via
  after_constructor, right Keccak env via prepared_environment/of_control;
  code/domain/endian from firstCall.leftCall/rightCall.fields, actual next heap
  words/alignment/room from new heap_bounds/words. Preserve input structure si56/
  64 via first own safe frame (fixed buffers before si, si+96<=public boundary),
  then paired_input_arguments supplies second actual loads. Initial sum of
  both caller allowances supplies second clocks via first packet lower bound.
  Full two-map room premise or two_map_room can supply initial/second room.
  Ghost logical-record metadata from any/decoded API must give fixed buffers
  before node logical records for prior dictionary preservation: count0 ->T,
  count>0 -> actual array. Existing conditional paired_initialization then
  yields both dictionary pairs at real runtime entry.
- Whole frontend decoded/header/startup reachability, complete runtime context
  replacement, gas/state/Q/heap potential/compiler/target resource bound and
  finite K still open. Claim infinity; no full verifier. Account41%,0resetcredits.
  Continue autonomously, no checkpoint stop.


### 2026-10-17 — derive both actual decoded initialization calls

- WitnessInputArgumentsAfterCall.input_field_geometry proves actual si word
  addresses are public and protected from fixed hash arenas below si.
  arguments_after_constructor retains si56/64 via the first actual own frame,
  binds nodedb, derives mapped loads and agrees both real second-call args.
- WitnessPairedEnvironment packages fixed metadata for original/replacement
  constructor code, alloc/table helpers and Keccak environments. after_constructor
  derives all next metadata from actual caller control and invariant fields.
- WitnessNextDecodedCall derives the second actual decoded call from the first
  actual result: actual decoded-array cells survive own-safe writes, input
  structure loads survive, hash metadata/code survive, actual heapEnd supplies
  the next heap word/alignment/range, combined room supplies next arena bound,
  and initial sum clocks plus first lower-clock frame supplies next allowance.
  No independent second ConstructorPairResult or second heap premise.
- WitnessDecodedInitialization.paired_decoded_initialization derives BOTH
  actual calls from initial decoded Records and fixed entry metadata, actual
  si40/48 and si56/64 cells, common caller relation/public memory and explicit
  room/clocks. Empty uses a ghost logical record base only for count0; physical
  null actual argument remains unchanged. Initial logical-record ordering
  derived in both branches. Existing paired_initialization yields both actual
  runtime-entry DictionaryPairs, locals/globals/FFI/public agreement and exact
  real initialization evaluation into runtime with nested lexical restores.
- Successful witness-next-arguments-v1.log1501,
  witness-paired-environment-v1.log1440,witness-next-decoded-call-v1.log1556,
  witness-decoded-initialization-v2.log1557targets, permitted axioms only.
  Failed initialization-v1 simplified count0 negation to True->False; replacing
  the incorrect rfl argument with simp contradiction fixed it. Never indexed
  failed log. Index4660modules/7614facts, incremental policy61525entries/
  2253768653bytes, memory1.5GiBused/29available,disk58%/123GiBfree.
- NEXT frontend/header reachability: actual decode_stateless_input allocation,
  output field stores and input Records/HeapInput/initial cursor propagation;
  header validation/parent and blockhash globals then preserve these contracts
  to run_attempt initialization. Need actual combined decoded count<=B/4 and
  frontend cursor<=arenaLower+128*B+1MiB, not arbitrary input.length bounds.
  Runtime contextual replacement and global gas/state/Q/heap potential plus
  quantitative compiler/candidate startup/target certificate remain open.
- User asked whole-task progress again: estimated45%, rough35-55% uncertainty,
  entire branch over main and task obligations, not file count or currentsubtask.
  Claim infinity, no finite bound/full verification. Latest account42%, no reset
  credits; account reset already used. Continue, no checkpoint stop.


### 2026-10-17 — actual three-list witness decoding and shared allocation budget

- Strengthened Input.BytesList.body_normal/caller_normal with complete actual
  BackingLayout.control, including the selected heap update. Body obtains it
  from the real variable-list call and read-only size-check tail; caller handles
  both empty/no-allocation and nonempty/allocation branches across its scopes.
  There are no other external callers besides the new Witness chain. Initial
  failed control-v1 needed an untyped congrArg intermediate before assigning
  the expected stripped-state equality; v2 successful1335targets.
- Input.VarList.Cursor gives nextCursor array N =word(arrayNat+16N), exact
  natural value, alignment and actual rounded allocator equality. The actual
  conditional control frame and real initial heap word imply the next heap
  word, monotonic cursor and <=arrayNat+4*sliceLength, including empty count0.
  Success decoded-array-cursor-v1.log1300targets.
- Input.Witness.Program extracts the literal three-call suffix at dropLeading39
  Header.body. arrays_shape proves all real node/code/header calls and their
  six field stores/return. list_arguments derives actual slice ABI values from
  wp/w0/w1/w2/wlen natural offsets. v1 needed trivial after simp reduced six
  equalities to True conjunction, and explicit first<2^64 instead of decide
  with free variable. v2 successful1337targets.
- Input.Witness.Fields proves both actual tuple stores into SI96, exact fields,
  no-clock payment, outside-cell frame and preservation of actual decoded
  arrays above SI. v1 required unfolding store aliases before rw and keeping
  row-number hypotheses and goal at the same actual-array alias. v2 success1339.
- Input.Witness.StoredListNormal combines the actual byte-list caller, two SI
  stores and resumed continuation. Normal execution yields Records, max item
  sizes/count limit, HeapInput, exact next heap, clocks, own earlier-word frame,
  complete control, real continuation and correct caller restore. success1340.
- Input.VarList.RecordsIntervalFrame.of_interval only needs preservation on the
  actual old array interval. witness_count_bound proves combined node/code
  counts <=(input.length%2^64)/4 from actual decoded Records and adjacent validated
  subranges; no bound on mathematical list length assumed. success1301.
- Input.Witness.Environment preserves byte-list metadata through actual control,
  other locals across tuple bindings, earlier decoded arrays through a later
  list's fresh allocation/SI stores, and other SI fields. success1342.
- Input.Witness.HeadersNormal derives the actual final header list call, cap256,
  max1024, fields72/80, actual heap/control/clocks/frames and same SI return from
  normal execution. Failed v1 accidentally supplied an unnecessary malformed
  term for a field proof; removed in v2 successful1343. Failed log not indexed.
- Input.Witness.ArraysNormal derives all three real decoder calls from normal
  nodeCall execution. Two earlier actual arrays and four earlier SI fields
  survive later calls/stores. All three Records, node/code item bounds, cap256,
  six real SI fields, HeapInput, exact intermediate/final cursors/alignment and
  finalCursorNat<=initialArrayNat+4*witnessExtent hold at the actual final state.
  Restores both outer call locals correctly. Source allowance6*encodedBytes+20
  and cost<=6*encodedBytes+9 deliberately loose; not a target bound. Initial
  validated adjacent witness offsets, source metadata/copy/layout/heap and
  combined arena room remain premises. v1 invalid tactic change at projection
  codeGeometry.1; introduced named actual cursor equalities. v2 checked; v3
  additionally retains both intermediate cursor equalities/alignment in result.
  witness-arrays-normal-v3.log1344targets, permitted axioms. Index4668/7629,
  policy61534entries/2253818207bytes. Claim infinity; no full verifier/finite K.
- NEXT connect witness prefix: actual wp/wlen declarations, short guard82,
  three-step offset-store while loop, actual ssz_check_offsets count3/min12,
  w0/w1/w2 loads, then new arrays_normal. Before that remains payload fixed-list
  fields, decode_requests normal/control/heap and request continuation reach.
  Actual suffix is dropLeading39 Header.body; source witness prelude after
  decode_requests+SI32 starts dropLeading30 Header.body. Initial request decoder
  reachability currently only carries through completed payload, not to witness.
  validate_headers later allocates n*8+8,n*32+32 and each decode_header plus
  real keccak output; it does not release heap. n<=256 from actual suffix.
  Need preserve all initial decoder data to run_attempt initialization and
  derive frontend cursor bound. Runtime/global/compiler/target certificate open.
- Account42% last fresh check, zero reset credits, reset previously used.
  Continue autonomously; user percentage status remains45% rough35-55%.


### 2026-10-17 — witness offset loop, validator and actual array entry (in progress)

- Checked Input.Witness.OffsetProgram literal shapes: prefix at dropLeading30
  Header.body is wp/wlen declarations + guard82; offsetBody is i declaration,
  actual while3 + count3/min12 validator, then w0/w1/w2 loads and nodeCall.
  Actual generated byte-address additions flatten wp/i*4/constant, so using
  Scalar.flat32 on a nested add was structurally wrong. Added exact offsetRead/
  offsetByte AST and semantic equivalence to Scalar.le32. v2 success1345.
- OffsetStep actual store/read/index increment, copied HeapInput, cells/frame
  check. v1 unqualified bind in simp was ambiguous; qualified QueryBranch.bind.
  v2 success1346. OffsetLoop all three actual rows, exact source-clock3, full
  control/copied input/non-i locals, all scratch cells and outside24-byte frame
  check. v1 induction hypothesis omits premises independent of generalized
  source/index; corrected application, v2 success1347.
- OffsetsNormal derives actual guard passage and valid offsets from a normal
  return through offsetBody; rejected real SszErr10/11/12 cannot continue.
  Actual i scope restored; next loadedBody run, code/globals/control, heap,
  non-i locals and outside-scratch frame retained. First normal-v1 needed
  untyped congrArg result before Prod.ext; v2 success1348. Added outside frame,
  rebuilt values/loads together witness-offset-frame-v1.log1350targets.
- OffsetValues derives first offset12 and ordered other actual le32 values <=
  wlen.toNat using raw scalar number bounds at arbitrary mathematical indices.
  success1349. LoadedOffsets executes three real mapped loads/declarations,
  correct w0/w1/w2 locals/other locals and actual nodeCall with all restores.
  success1349. ArraysEntry connects offset loop+validator+loads to actual
  nodeCall, derives ordered geometry/locals, full control, copied bytes,
  outside-scratch frame, <=8 source clocks and exact restore stack. success1351.
- ArraysNormal full conclusion now has name ArraysResult to keep subsequent
  composition statements readable. Its existing checked proof unchanged except
  unfolding this definition. Full dependent closure successful
  witness-array-result-v1.log1351targets. Indexed4675modules/7642facts. No finite
  K/full verification. Last account43%, no reset credits.
- PENDING: Witness.BodyNormal combines ArraysEntry and ArraysNormal, but v1
  kernel deep-recursion failure at maxRecDepth10000 after ~18GiB RSS; no failed
  logs indexed. v2 extracts arithmetic into private scalar lemmas, but was
  still running in session44016 at this note (witness-body-normal-v2.log).
  This batch also tried PrefixNormal and its old revision failed numeric simp
  matching; source since fixed by exact difference after simp and explicit
  modular length reduction. PrefixNormal remains unverified until next build.
  New ControlFields.lean drafted, unverified: generic Environment.of_control
  and global_of_control. Use these opaque bridges and trans rather than rw in
  BodyNormal if v2 repeats kernel failure. Do not kill/restart live build based
  only on elapsed time; resource guard24GiB active. Do not index failed batch.
- Main remaining plan: complete witness prefix/offset/array composition,
  then earlier payload/fixed-list/request parsing, actual validate_headers
  reachability/frame/cursor, connect derived records/layout to paired decoded
  constructors; whole runtime/global gas/state/Q/heap/compiler/target bound and
  final certificate still open. User status estimate45%, rough35-55% remains
  whole-task judgment; no file-count interpretation or finite certification.


### 2026-10-17 — user corrects the objective: unchanged program, no numerical ceiling

- User explicitly rejected the replacement route: bound the CURRENT Pancake
  implementation. It should not be overly loose, but need not be below ANY
  number. Confirmed the previous score-cap-driven objective was wrong.
- Updated authoritative objective and seven-step plan at top of bound.md.
  Retired radix replacement, cross-program equivalence, changed candidate ROM
  and below-cap feasibility gates. No new candidate implementation work.
- Pinned current main 7d656e5b6878aa420de793d9d6f689fa26ec0842. Checked fixed
  Guest/Ast.lean, Guest/guest.pp.pnk, Solution.lean and claim.json have no diff
  from main. No running Lean/build process remained at the scope correction.
- Preserve all existing files/history; original-program proofs can depend on
  shared helpers under WitnessRadix despite that directory's name. Reassess
  applicability by statements. Replacement-specific theorems are off the active
  path. The ~2.1005e16 construction allowance is a conditional partial upper
  bound and its exceeding a Yukon cap is irrelevant, not a blocker.
- Immediate next work: original-program proof/budget inventory, original table
  construction/query accounting and unresolved global gas/state/Q/heap work.
  Explicit units and phase arithmetic, no artificial threshold or algorithm
  changes. Continue deriving actual entry premises and tighten major slack.
- Interrupted previous build had actually completed: witness-body-normal-v3.log
  1353targets successful, permitted axioms, 2.7s for BodyNormal. Opaque generic
  ControlFields + direct trans/congrArg replaced expensive rewrites; v1/v2
  kernel recursion failures are not evidence. PrefixNormal and ControlFields
  passed witness-control-prefix-v2.log1347targets. These are original decoder
  proofs, reusable, and may be indexed from successful logs only.
- No full-program finite bound/certificate/full verification has been achieved.
  Prior conversational45% concerned the wrong plan and is withdrawn as an
  estimate for the corrected objective. Account last43%, no reset credits.


### 2026-10-17 — cleanup added to corrected plan

- User explicitly requested a cleanup item to remove unneeded code, including
  the replacement Pancake implementation, and delegated its timing.
- Added mandatory cleanup after the original-program dependency inventory,
  with a final sweep before final validation. Remove branch-added replacement
  code, replacement-only equivalence proofs and associated generators/test
  harnesses/candidate artifacts. Preserve/extract shared helpers needed by the
  unchanged program's proofs; do not delete whole folders based on their names.
- Update imports/build metadata/evidence indexes, check retained dependencies,
  and confirm baseline program/artifacts unchanged. This supersedes earlier
  preserve-all guidance; history remains available in Git. No deletion yet.


### 2026-10-17 — original dependency inventory and replacement cleanup underway

- Read the corrected plan and continued autonomously. Inventory roots cover
  original bootstrap, witness construction/lookup, input reachability, local
  gas, abstract global accounting and compiled work. These are applicability
  entry points, not a claim of closed global obligations or a progress metric.
- Extracted generic state/local operations, declarations/restoration, loop
  traversal, control projection, table header, dictionary result values,
  original constructor syntax/allocation geometry and hash environment frames.
  Historical namespaces are retained for compatibility. Original record/table
  preparation now proves its own environment frame directly.
- The original roots have zero import dependencies on replacement AST modules.
  Removed 256 replacement-only/unreferenced Solver modules, the replacement
  Pancake source, generator, harness and generated candidate/test artifacts.
  Every removed file was checked absent from main. Compact source hashes and
  grouped artifact manifests are in original-plan-cleanup.json; Git retains
  committed history. Removed cached products for deleted Solver modules too.
- Reduced shared Model/ByteKeys/WordBits/Graph/Addressing modules to dictionary
  semantics, keys, bit arithmetic, slice types and ordinary address helpers;
  removed the replacement pure tree implementations. Retained helpers under
  WitnessRadix are used by unchanged-program proofs, not a replacement guest.
- Dropped stale/deleted module and theorem evidence entries. Structural import
  isolation and baseline identity checks pass; retained Lean closures are being
  rebuilt before committing the cleanup. No full verification or finite bound.
- Build attempts original-import-cuts-v1/v2 were interrupted after concrete
  missing-import failures (mask7, generic declarations) and were not indexed.
  Foundation v1/v2 exposed formerly transitive Mathlib imports (Classical.decEq,
  by_contra); fixed explicit imports. These failed logs are not proof evidence.
- Account usage last44%; zero reset credits remain.


### 2026-10-17 — replacement cleanup validated; original summed budgets checked

- Removed258 replacement-only/unreferenced Solver modules in total, including
  the last mixed original/radix preparation-agreement module. Kept the actual
  original run_attempt call-shape/argument lemmas in OriginalWitnessEntry.
  Deleted the replacement source, generator, harness, generated candidate and
  test artifacts. All deletions were absent from main; Git retains history.
- Original foundations: original-foundations-v3.log701jobs, successful,
  3:58.77 wall time, 1,711,624KiB maximum RSS. Original entry points:
  original-retained-closure-v6.log1532jobs, successful, 3:25.54,
  2,275,728KiB maximum RSS. Both use the24GiB memory guard.
- Full affected closure:601 Solver modules through22 leaf targets, recorded
  with source hashes in original-plan-validation-targets.json. Successful
  original-affected-closure-v3.log1618jobs,4.45s final cached validation,
  1,867,160KiB maximum RSS, permitted axioms. This checks helper dependencies,
  not the full verifier/comparator/kernel replay or a finite certificate.
- New WitnessBuildVariableLoop/Populate/Execution check the entire original
  constructor body with a sum of actual record lengths/insertion indices.
  WitnessBuildBudget proves exact source-clock decomposition, the triangular
  index sum, and aggregate hashing-byte bound. RecordByteBudget proves actual
  decoded payload sum+4*count<=encoded list length, including empty items/lists.
  WitnessDecodedBudget derives215*N+7*triangle(N)+20*((B-4*N)/136)+46.
  Entry/code/arena/sufficient-clock premises remain; this is not target K.
- PlacementDistinct proves that repeated keys add no occupied slot to a
  covering list. WitnessDictionaryDistinct applies that result to actual
  original lookup execution, giving6*D+3 source clocks for D distinct observed
  keys rather than6*N+3 for N records. Arbitrary duplicates/query alignment
  are covered; no Keccak randomness, injectivity or collision resistance used.
- Failed affected-closure v1/v2 logs were not indexed. They exposed one last
  replacement-only mixed lemma, a copied unfold name, and Nat.zero_add/let
  normalization in the decoded arithmetic. Corrected them and indexed only
  successful complete logs. Earlier retained v1-v5 failures were missing
  explicit generic imports and residual replacement lemmas; no failed log is
  proof evidence. Final evidence4434 modules/7222 printed facts after pruning
  stale/deleted source records and removed theorem names.
- Refreshed offline witness-table-budget utility/report for the corrected
  objective: removed Kmax comparisons and failure decisions tied to Yukon.
  Proposed literal target prices remain conditional inspection, not checked
  execution costs. Optimizer logic/self-tests are unchanged.
- Inventory confirms zero missing Solver imports, zero replacement-AST
  dependencies, and unchanged fixed Guest/InitE/ROM/original-proof files.
  Incremental policy passes61306entries/2252644684bytes. Claim stays infinity.
- Next global obligation: actual process_transaction regular root budget
  mgas=min(16777216-intrinsicRegular,executionGas), its validation/caller/TE/MSG
  initialization, plus the six literal system roots. Carry the checked ledger
  across successful-child log/delete merges, rollback and block counters.
  Whole runtime, global invariants and quantitative baseline target transport
  remain open. Account last45%, no reset credits.


### 2026-10-17 — actual validator and root split checked

- RootValidationProgram identifies the complete unchanged validate_transaction
  body. NormalCallEntry/Data, NormalDeclarationEntry and PureGuard invert real
  normal runs without assuming successful reads, helper results or clocks.
- RootValidationNormal/ValidatedResult derive the actual returned three-word
  intrinsic value, with regular and floor components <=16777216. RootValidationCall
  connects that postcondition to the real scoped call in process_transaction.
- RootProgram/Execution/Entry check the actual min split, lexical scopes, liquid
  and reservoir words, the one source clock consumed and the liquid+regular cap.
  This is not the whole caller/frame proof, nor a runtime bound for preprocessing.
- Successful original-root-entry-v2.log covers the new closure (1087 jobs).
  Earlier numbered attempts failed during proof development and are not evidence.
  Index4446 modules/7251 printed facts;4457 Solver modules, no missing imports or
  replacement dependencies, fixed program/artifacts unchanged. Incremental policy
  passes61318entries/2252698656bytes, not full verification. Claim remains infinity.
- Inspected actual op_sstore: state refunds restore a slot with zero original
  value to zero. Existing StorageDebt captures the balance, but the real backend,
  child/rollback and global signed accounting connection is still open. Do not
  assert the earlier conditional380M gas allowance as an established global fact.
- Continuing actual caller-local transport and TE/MSG/frame initialization, then
  global ledgers and quantitative unchanged-target transport. Account47%, no
  reset credits. No whole finite bound yet.


### 2026-10-17 — caller transport and actual fresh-frame clear checked

- LocalPrefix and LocalPath prove normal continuation reachability and saved
  local/code/exception-table preservation across arbitrary scoped helper calls.
  RootCallerProgram checks the complete original prefix, including the blob-fee
  conditional. RootCallerNormal composes actual validation, caller transport
  and root split. RootNormalEntry derives both scalar reads and the available
  min-call clock from a normal run. No intermediate helper success is assumed.
- Successful original-root-caller-normal-v1.log1094jobs, permitted axioms.
  WordOperationNormal and NormalCallClock cover the required read/clock inversion.
- Arenas.Program/Execution/Arithmetic/Calls/Marks check the unchanged upward and
  downward allocators and marks. Natural aligned room implies both actual guards;
  allocation changes only its correct global cursor, preserving all memory/FFI.
- FrameNewProgram identifies the actual first four calls of frame_new.
  FrameNewZero executes both marks, 280-byte scratch allocation and full memzero,
  with exact scopes, memory and15-source-clock cost. Every complete frame word
  is zero, including64/184/192; the clear preserves every outside word. Entry
  code/cursors/alignment/room/mapped region/clock remain explicit and must be
  derived from the caller/arena invariants. Later frame initialization remains.
- Successful combined frame-new-zero-v3.log1102jobs includes the new caller and
  frame closures. Development failures local-prefix-v1, local-path-v1, root-caller-v1,
  normal-word-clock-v1, arena-execution-v1, arena-mark-v1, frame-new-zero-v1 were
  proof/notation normalization errors; only completed successful logs are indexed.
- Evidence4460modules/7278printed facts;4471Solver modules. Inventory reports no
  missing imports/replacement dependencies and unchanged source/semantics/ROM/
  fixed proofs. Incremental policy refreshed, not full verification. Infinity;
  no whole-program finite bound or target K yet. Account48%, no reset credits.
- Continue message gas-to-frame cells and helper memory frames, successful child
  merging/rollback and actual signed block gas, then aggregate source work and
  unchanged compiler/target transport. No numerical ceiling applies.


### 2026-10-17 — physical frame initialization through jump-destination entry

- PanFieldStores proves real scalar initialization sequences with exact memory
  writes and protected source reads. Expected words are specification data;
  the original runtime local/copy expressions are retained.
- FrameNewFields checks all seven actual stores preceding compute_jumpdests;
  used/spill stay zero and the actual regular ledger equals MSG_GAS.
- FrameNewAllocation checks both real scratch/frame-memory allocations and
  three stack stores, deriving guards/results/frames from natural room and
  code/cursor/clock premises. These operations preserve all regular cells.
- FrameNewInitialization composes that actual suffix. FrameNewFresh joins it
  to the earlier actual allocation/clear, deriving both zero counters and all
  intermediate local values, preserving incoming message words, and exposing
  the real continuation at compute_jumpdests. Exact prefix cost17source clocks.
- Explicit remaining entry premises: correct fixed code, global cursors, arena
  room/alignment, mapped frame/message words, physical separation and enough
  clocks. This is an actual source prefix theorem, not a whole frame return,
  pricing of straight-line work, whole-program gas ledger or target K.
- Successful frame-new-fresh-v2.log1107jobs includes RootCallerNormal and all
  new dependencies. Development failures field-stores-v1, frame-new-allocation-v1,
  frame-new-fresh-v1 were notation/normalization issues; no failed log is indexed.
- Evidence4465modules/7297printed facts;4476Solver modules. Inventory now includes
  actual root initialization roots. No missing imports/replacement dependencies;
  pinned Guest/InitE/ROM/fixed proofs/claim unchanged. Incremental policy passes
  (not full verification). Claim infinity; no whole finite runtime bound yet.
- Next: original compute_jumpdests/lst_new_scratch/htab_new_scratch memory frames
  to preserve initialized gas through frame_new return; actual caller MSG gas
  construction and successful child merges/rollback/block signed accounting.
  Account last48%, no reset credits. No numerical ceiling applies.


### 2026-10-17 — complete unchanged jump-destination helper checked

- JumpDest.Program is kernel-checked against the complete original body.
  Arithmetic/Reads/Continuation/Advance/Mark/Branch/Step derive every actual
  opcode branch, conditional lookahead, bitmap update and positive1..33 advance.
  StepMapped derives byte and bitmap reads from mapped regions; no opcode oracle,
  content restriction, cryptographic premise or frozen code-byte assumption.
- Loop proves the entire actual scan, with at most n-index iterations/source
  clocks and a complete final-state formula. All earlier words above the bitmap
  survive every iteration; source scope/counter restoration is included.
- Execution/Environment/Call compose actual scratch allocation, memzero, scan,
  return, code lookup and scoped caller ABI. Incoming-cursor upper memory is
  preserved, scratch cursor updated exactly, FFI/other canonical fields retained.
- Caller source-clock allowance n+memzero_price(bitmap_bytes(n))+3; conditional
  literals131588 for n<=131072 and65796 for n<=65536. Code/domain/cursor/alignment/
  room/clock premises remain; actual length and ownership reachability, weighted
  straight-line/target work and whole runtime are not claimed.
- Removed unused preliminary abstract opcode advance model after the actual
  word selector was connected to execution. Removed its two stale printed-fact
  index entries. Retained rebuild jumpdest-retained-v1.log1120jobs succeeds and
  includes RootCallerNormal/FrameNewFresh. Permitted axioms only. All development
  failed logs remain unindexed; final retained source hashes indexed.
- Evidence4478modules/7330printed facts;4489Solver modules. Inventory includes
  JumpDest.Call under actual root initialization. No missing imports/replacement
  dependencies; pinned source/semantics/ROM/fixed proofs unchanged. Incremental
  policy passes61352entries/2252867078bytes (before the small arithmetic cleanup),
  not full verification. Claim infinity; no whole-program finite K yet.
- Continue applying the memory frame to frame_new and proving the actual
  lst_new_scratch/htab_new_scratch helpers and final stores/count reads. Then
  caller MSG construction, successful child merges/rollback/signed block gas,
  global work aggregation and unchanged target transport. Account49%, no resets.


### 2026-10-17 — unchanged scratch helpers and two-sided memory frames

- Actual lst_new_scratch: header/buffer allocations, three stores, return/scopes;
  body2/caller3 source clocks. Actual htab_new_scratch(20,4): six allocations,
  all nine header stores, short used-byte clear, return/scopes; body11/caller12.
  Aligned natural room derives guards; exact final scratch cursor and memory.
- Both preserve memory below frame_mem_ptr and at/above incoming scratch_ptr.
  JumpDest Mark/Step/Loop/Execution/Call now exports the same two-sided frame,
  retaining its upper-only loop wrapper for existing consumers.
- Arenas Prefix/PrefixFields/DownPlan support actual allocation/store segments;
  no replacement program. PanFieldStores now supports actual global reads.
  GasBudget.TableCount proves actual declaration and assignment calls,1clock.
- Successful combined scratch-helpers-count-v1.log1110jobs, explicit time exit0,
  allowed printed axioms. Earlier scratch-two-sided-v1.log1099jobs succeeded.
  All current helper sources indexed,4492modules7371facts; counts not progress.
- Inventory includes both constructors/count getter; unchanged pinned source,
  semantics, ROM, fixed proofs, Solution and claim. Incremental policy refreshed;
  no full verification, no finite whole runtime bound. Claim remains infinity.
- Continue actual frame_new suffix/return and initialized ledger preservation,
  then actual root message construction/global accounting and unchanged target
  transport. Account1%,0manual reset credits; no numerical ceiling.


### 2026-10-17 — complete unchanged frame constructor and caller

- FrameNewSuffixProgram checks the exact full afterGas AST. Counts executes both
  real htab_count calls (the second assigns acc_n), all final stores/global
  reads and return; regular ledger cells64/184/192 survive.
- SuffixData tracks exactly six external word reads and new frame slots;
  natural outside-frame ownership gives store separation and both-sided helper
  frames. Delete/Logs/Suffix compose every actual helper and scope to return,
  preserving incoming initialized regular ledger; costprice+n+20source clocks.
- FreshFields derives prefix e/msg/empty bindings and all external-memory
  preservation through the actual clear/allocations/stores. Geometry proves
  exact original reservationbitmapBytes(n)+2656, without alignment slack.
  Mapped derives bitmap/log/table/used mappings from one live arena interval.
  FreshCanonical proves exact final global update normalization.
- Execution joins the17-clock prefix to the complete suffix; all intermediates
  and helpers derived. FrameNewEntry records only actual entry conditions;
  Call proves real callee environment, caller ABI and lexical restoration.
  Returned regular ledger=MSG_GAS. Caller source allowanceprice+n+38; conditional
  n131072=>131623,n65536=>65831. Not target K or all-caller length reachability.
- Successful frame-new-call-v1.log1154jobs includes RootCallerNormal and complete
  retained constructor closure, explicit exit0 and only permitted axioms.
  Development failures counts-v1/v2, suffix-data-v1, delete-v1/v2/v3,
  suffix-v1/v2, fresh-fields-v1, execution-v1 were corrected proof normalization,
  free-metavariable or record-projection issues; never indexed failed logs.
- Refresh inventory/policy/baseline identity. No whole finite runtime bound,
  full verification or claim change. Account2%,0manual reset credits. Continue
  capped root mgas through actual TE/MSG stores and caller initialization,
  then child merges/rollback/block signed ledger and unchanged target work.


### 2026-10-17 — actual capped root gas reaches TE and MSG memory

- LocalPrefix now covers actual stores, standalone/assigned helper calls,
  ordinary declarations and while loops. LocalLoopSummary proves preservation
  by evaluator-clock induction, denying escaping return/break/continue; this
  does not assume body success or establish an iteration/runtime budget.
  Existing LocalPrefix.summary API retained; summary_full supplies stronger
  loop information. LocalPathTactics constructs kernel-checked structural
  proofs for actual ASTs, failing on unsupported instructions.
- RootTeProgram/Normal checks exact post-split prefix through TE_GAS; actual
  normal store derives base-word read, mapping, exact write and physical cap.
  RootMsgProgram/Normal covers the full actual prefix through MSG_GAS,
  including both access-list loops and optional blob/setcode branches. Actual
  validator/root split gives storedGas.toNat+intrinsicRegular.toNat<=16777216.
- Neither theorem prices preprocessing or proves later mutable-map/helper
  preservation of MSG_GAS. That ownership/reachability gap remains explicit.
- FrameNew complete body/caller strengthened with a memory frame for every
  word outside its incoming live arena, to support parent/global accounting.
- Successful root-msg-normal-v2.log1161jobs, explicit exit0, allowed axioms.
  Root-te-normal-v1, local-loop-prefix-v2, root-msg-program-v1 also successful.
  Failed development logs are not indexed. Evidence refreshed on successful
  combined current sources; counts are not task-completion metrics.
- Continue message/map ownership and active frame_open, successful-child
  merges/rollback/block signed accounting, then phase/unchanged target bounds.
  Pinned program unchanged; infinity, no whole finite K or full verification.
  Account last2%,0manual reset credits; no numerical ceiling.


### 2026-10-17 — active frame_open initialization and caller checked

- FrameOpenProgram checks exact original AST; continuation MSG is offset40,
  not24. Stores executes four real field writes and both typed global assigns.
- Record derives104-byte allocator guards, exact clear/stores/activation,
  return/scope,6source clocks; child regular ledger and all memory outside the
  live allocation preserved. Geometry proves post-frame_new cursor number,
  alignment, extra104-byte room, totalbitmapBytes(n)+2760 reservation.
- Execution joins parent declaration, whole frame_new and continuation record;
  Call derives actual two-argument callee environment and real scoped caller.
  Active child's regular ledger=MSG_GAS, canonical globals/FFI/domain retained
  except four intended pointer updates, outside incoming live arena unchanged.
  Caller source allowanceprice+n+45; not target K or caller reachability.
- Successful frame-open-call-v1.log1168jobs includes RootMsgNormal and all new
  frame closures; explicit exit0, allowed axioms. Development failures stores
  v1/v2, recordv1/v2/v3, geometry-depth and executionv1 were corrected AST-offset,
  continuation-expression, arithmetic normalization or recursion-depth issues.
  Failed logs not indexed. Final current source closure indexed.
- Continue actual message/map preprocessing ownership and global ledgers,
  successful-child suffix merges/rollback, signed block accounting and source
  work aggregation/unchanged target transport. Claim infinity; no whole finite
  bound/full verification. Account last2%,0manual reset credits.


### 2026-10-17 — persistent TE/message allocation contracts

- Input.FreshRecord checks both original te_new200byte and msg_new176byte
  bodies via their exact actual allocator/clear/return scopes. Allocator guards
  derive from natural heap room; full zero memory and9body clocks.
- FreshRecordCall checks zero-argument caller environment/ABI,10caller clocks,
  exact heap extent without alignment padding, and both-sided outside-memory
  preservation. Generic foreign state: no additional host assumption is needed.
- Successful fresh-record-call-v1.log1065jobs, explicit exit0, allowed axioms.
  Initial fresh-record-v1 failed only for missing specialized host-type import;
  removed that unnecessary specialization and checked the generic proof.
- Original entry code/heap/domain/alignment/room/clock remain explicit. Warm
  map construction/queries/growth/deletion and caller ownership remain open;
  no finite whole runtime bound/target K or full verification. Account3%,0credits.
- Next: general original mutable-table runtime/ownership contracts for20/52/60
  byte keys, then connect root message to active-frame and global gas ledgers;
  preserve pinned program and no numerical ceiling.


### 2026-10-17 — actual20/52-byte hash and aligned comparison callers

- HashSized proves actual aligned and unaligned20/52-byte unrolled hash cores,
  including all byte macros, word assembly, XOR folds and final avalanche.
  Execution wraps actual h/w declarations/scopes; Call proves actual two-word
  ABI and one caller source clock, exact result and pure canonical frame.
  Reproducible proof-syntax generator generate-hash-sized.py changes no program.
- MemeqSizedProgram checks real20/52-byte fast blocks. Fast executes complete
  actual memeq body through every early mismatch/success and i scope. Reads
  discharges every comparison/alignment expression from concrete input words,
  tail bytes and locals; Call proves actual three-word ABI and one caller clock.
- Successful hash-sized-call-v1.log1194jobs (also root MSG, frame_open, fresh
  records), memeq-sized-call-v1.log1092jobs (both new key-helper closures).
  Explicit exit0, permitted axioms. Failed hash-sizedv1/v2 were finite numeral
  normalization; memeq-fastv1 used Value where evaluator result was required;
  both corrected and failed logs unindexed. No source/ROM/semantics change.
- Remaining: unaligned variable-length byte-loop comparison;60-byte hash;
  actual generic map probes/insertion/growth/backshift deletion/order/truncation
  and cumulative ownership/counts. Input/read/code/clock entry conditions remain
  explicit; helpers do not establish whole runtime or target instruction work.
- Inventory/policy/evidence refreshed. Infinity, no whole finite K/full verifier.
  Account3%,0manual reset credits. Continue full original runtime plan.


### 2026-10-17 — small-key byte fallback and uniform mapped callers

- MemeqByteRuntime Program/Bodies/Control/Tail/Blocks execute the actual8-byte
  and final-byte loops, including every early mismatch, finite progress and
  final return. Induction uses remaining byte count; no execution oracle.
  Price length/8+length%8 in body, pure canonical state. Execution includes
  skipped aligned branch, actual i declaration and lexical restore.
- Mapped derives actual byte loads from mapped source memory, with arbitrary
  contents; Call proves the real ABI, answer0or1 and paid+1caller clocks.
  Supports all lengths<=64, including20/32/52/60. Literal callers7/5/11/12;
  no full60-byte aligned comparison/hash contract claimed yet.
- MemeqSizedMapped derives every fast word/tail-byte read and both alignment
  branches, using mapped byte regions and no-wrap input footprints. Uniform
  actual20/52-byte comparison callers bound7/11, preserving memory/FFI/globals.
  HashSizedMapped derives uniform actual20/52-byte hash input reads/caller,
  either alignment, exact observed digest, one caller clock, pure frame.
- Successful key-helpers-mapped-v1.log1216jobs, explicit exit0, permitted axioms;
  includes RootMsgNormal, FrameOpenCall and FreshRecordCall closures. Earlier
  byte-runtime-control-v1, memeq-byte-runtime-call-v1 also succeeded. Failed
  tail/block/entry/mapped development checks were corrected source-clock or
  opaque-rank normalization/namespace errors; failed logs unindexed.
- Actual table-probe progress, ownership/order/count invariants, growth,
  backward-shift deletion/truncation, full gas/phase/target accounting remain.
  No finite whole runtime bound or full verification; pinned program unchanged.
  Account last3%,0manual reset credits. Continue with actual generic probes.


### Original20/52-byte lookup bodies and callers

Checked the complete original htab_find_slot and htab_get bodies/callers, including real header reads, uniform mapped-byte hash/comparator calls at every alignment, masked start, all collisions, scopes and actual value reads. A binary-used covering list D<capacity yields a finite probe chain without a distribution assumption. Find caller allowance8D+2/12D+2; get caller8D+3/12D+3 source clocks for20/52bytes. All nonlocal state is pure. Physical representation, room/mapping/no-wrap/code/clock premises remain explicit. Runtime facts do not claim full key dictionary semantics, mutation invariants, whole runtime or target K. Successful find-sized-build-v1.log1111jobs, find-sized-call-v1.log1117jobs, get-sized-call-v1.log1129jobs; final log includes the full retained changed closure and permitted printed axioms. Pinned baseline and infinity claim unchanged.

Original membership body/caller also checked: real htab_has returns0or1 through its actual capacity test after all probes; same8D+3/12D+3 source-clock allowance and pure nonlocal state. has-sized-call-v1.log1132jobs, exit0, permitted axioms. Inspection of original constructors also identifies28/60-byte indexed keys; fallback hash/aligned comparisons at those widths remain to be covered.


### Original indexed-key hash/comparator fallbacks

Checked the whole actual generic hash body and caller at other small lengths, including28/60-byte indexed keys. Every byte read/fold, eight-byte/trailing-byte loop, avalanche operation and scope is derived; exact body cost length/8+length%8, caller+1. Extended actual memeq through its previously uncovered aligned32-byte and8-byte word loops, then both byte fallback loops and final return. Derived all physical reads from mapped regions at arbitrary alignment. Uniform28/60-byte comparison caller allowances8/12source clocks; no memory/control/FFI changes. Successful memeq-other-mapped-v1.log1119jobs, exit0, permitted axioms, includes hash-byte-call-v1 and all dependencies. No whole bound, original28/60lookup, mutation or target K claimed. Original sources, fixed proofs, ROM, Solution and claim remain unchanged.


### Original28/60-byte indexed lookup/retrieval/membership

Composed generic mapped hash/comparison callers with the actual header reads, masked start, finite physical occupied chains, lexical scopes and get/has suffixes. Actual find callers cost at most9D+9/13D+13; get/has9D+10/13D+14 source clocks for28/60byte keys. Worst-case collisions and either alignment are covered without a hash distribution assumption. Binary used slots, D covering occupied slots and D<capacity, physical mapped/typed regions, no-wrap/code/entry-clock premises remain explicit. Successful indexed-query-call-v2.log1255jobs, exit0, permitted axioms; retained root MSG and active frame initialization also included. Whole-program finite/target bound and actual map mutation/count/ownership reachability still open. Claim infinity and pinned main bytes unchanged.


### Whole original raw-insertion body and caller, every key width

Checked actual seven headers, real hash, masked empty-slot scan, real generic memcpy from byte regions at either alignment, all five value/used/order/order-position/count writes, scopes and actual ignored-result ABI. Exact final memory and physical count+1 derived. Caller bound D+hashPrice+bytePrice+2 gives D+9/17/7/13/25 for20/28/32/52/60bytes. Physical GeneralData is independent of callee parameter names and transports by exact nonlocal fields; actual code lookup supplies t/key/value locals. Source data and all per-slot mapping/no-wrap/header protection/coverage/clock premises remain explicit. Actual growth/deletion/ownership invariants and aggregate counts, whole runtime, compiler/target bounds open. Successful insert-general-call-v1.log1146jobs, exit0, permitted axioms. Includes scan-count and mapped-copy facts, generic all-width hash dispatcher and byte-view construction. Baseline and infinity claim unchanged; no full verification.


### Common original query contract and cleanup

Unified actual mapped comparator callers for every original key width, including32-byte physical byte views. One common occupied-chain/find/get/has family now covers all five widths, preserving prior per-width bounds and exporting returned-index<=capacity for every lookup. Removed20 superseded width-specific runtime query proof modules and160 stale build artifacts/14,780,408bytes after zero external importers were checked. Retained shared original helpers and logical32-byte witness proofs. query-runtime-cleanup.json records scope/source hashes. Successful general-query-cleanup-v1.log1267jobs, exit0, permitted axioms, includes raw insertion and retained root/frame contracts. Global mutable ownership/count/growth/deletion and whole runtime/target K remain open; baseline bytes and infinity claim unchanged.


### Whole original htab_set when the actual guard excludes growth

Checked real setter suffix/body and ignored-result caller for all five key widths, with actual lookup, update-or-insert decision, complete raw insertion when absent, real no-growth guard, scopes and exact memory/control/clock frame. Physical count remains count or increments count+1. count<=D and2D+2<=capacity supply the guard and exclude count-word wrap. Caller source allowances9D+12/10D+27/7D+10/13D+16/14D+39 for20/28/32/52/60. Successful set-no-growth-budget-v1.log1161jobs, exit0, permitted axioms; preceding set-no-growth-call-v1.log1160jobs. GeneralData.find_call bridges shared physical insertion ownership to actual query code. Source data/count/room/code/clock premises remain explicit; no actual growth/deletion/global/target bound or logical map spec claimed. Next: natural pool layout ownership, actual growth, mutation invariant and deletion/rollback.


### Original table pool ownership and physical runtime model

Checked generic natural layouts for all original key widths: six fresh allocations and five relocated arrays with a prior header on either side. Used padding is explicitly owned. Exact constructor stride word expression, ordinary-domain mappings/no-wrap and cross-pool separation derive every SlotData field, including header protection for actual memcpy and metadata stores. Physical Header/Occupied predicates describe all nine real header words, binary used slots, dense order and inverse position arrays without logical-key/cryptographic assumptions. Header+Occupied+geometry derive complete table-side GeneralData for query/raw insertion/setter contracts; query mapping/code/endian/capacity/order room remain explicit. Success table-memory-entry-v1.log1272jobs, exit0, permitted axioms; retained root/frame/no-growth setter closures included. These are conditional representation/geometry facts. Actual generic constructors must establish the model and mutations/growth/deletion must preserve it; no global/target finite K.


### Complete original generic htab_new and physical initial model

Checked entire original persistent constructor and real scoped ABI for all five key widths: six real allocators, exact stride, all nine header stores, cap4/multiple8 clear paths, return/scopes, exact heap cursor/memory/clock, and outside-reservation memory frame. Exact caller source price12 at cap4, otherwise Zero.price(cap)+8. Reservation72+(stride+24)*cap+round8(cap); if cap%8=0,72+(stride+25)*cap. Actual completed headers and zeroed used bytes establish empty Header/Occupied including dense order/inverse-position arrays, then derive complete table-side GeneralData for checked runtimes. Source query mapping, code/domain, initial heap cursor, valid allocated room/alignment, capacity shape/power and clock remain caller premises. Strengthened raw insertion's actual body/caller with original selected-slot-used0 fact; added full generic untouched-word frame and proved all nine header meanings preserved/count+1 from actual copy/stores. Successful combined table-runtime-budget-v1.log1309jobs, exit0, permitted axioms; retained root gas/frame/no-growth setter closures included. Actual occupied/order mutation preservation, growth/deletion/rollback, whole phase/target K still open. Baseline and infinity claim unchanged.


### Actual lookup selection and no-growth setter effects

Strengthened the real all-width probe/body/caller with Selection: returned sentinel or physically occupied in-range slot. Snapshot memory/domain/endian transport is explicit. Binary used coverage derives used1 and membership for present results; empty tables force absence. Strengthened actual setter suffix/body/caller with exact Effect: occupied value update or generic raw insertion into a used0 slot, including concrete memory formula. Existing prices/counter/no-wrap facts unchanged. Success find-general-selection-v1.log1170jobs (all query leaves), set-no-growth-effect-v1.log1163jobs, exit0/permitted axioms. Full occupied/dense-order/inverse-position preservation and growth/deletion/global/target K still open.


### 2026-10-17: original mutable-table representation preservation

The common actual lookup exports absent-or-occupied selection; the no-growth setter exports its exact update-or-insert memory effect. Complete physical representation preservation is now checked for the original value update and raw insertion, including shared-word used-byte writes, dense order append, inverse positions and all nine header meanings. Actual insertion_call and setter_call compose executed mutations with these models; no logical key equality, favorable collision or injected mutation execution is assumed. The setter still requires the explicit no-growth guard; all actual code/query/domain/little-endian/ownership/clock premises remain explicit.

Successful logs: find-general-selection-v1.log (1170 jobs), set-no-growth-effect-v1.log (1163), table-value-model-v1.log (1150), table-insert-fields-v1.log (1158), table-insert-append-v1.log (1160), table-insert-model-v1.log (1161), table-set-model-v1.log (1173), table-set-model-call-v1.log (1181), final combined table-mutation-model-v1.log (1220). All explicit exit0 and permitted printed axioms. The initial table-insert-arrays-v1.log failed on a dependent Decidable rewrite; simp only with the checked address equivalence resolves it. No failed log was indexed. These source-clock/state facts are not a whole-program finite bound or official verification. Remaining: actual growth/rehash and deletion/rollback, global ownership/count/gas/phase accounting, compiler/target transport. Baseline program/semantics/ROM/Solution/claim unchanged. Account usage8%,0 reset credits at the latest read.


### 2026-10-17: complete unchanged mutable-table growth

Checked the full original htab_grow body and actual caller for all five original key widths. Six old-header reads/doubling, all five real allocations/rounding/cursor changes, actual clear, seven reset stores, signed original while comparison, every old dense-order read/raw-insertion call, return and declaration restoration compose. Old array snapshots remain readable throughout rehash. Actual post-call physical header/binary occupancy/dense order/inverse positions and unchanged count are derived; the original setter growing suffix then executes its extra insertion and proves count+1/model preservation. Occupied.length_le derives D<=C; growth_shape derives new bits/clearing shape from old power/minimum and owned extents. Source caller allowance: Zero.price(2C)+triangle(D)+cD+7, c=10/18/8/14/26 for20/28/32/52/60. Exact reserved five-array space (stride+25)*2C; header reused.

Final complete successful closure: table-grow-complete-v1.log (1294 jobs), explicit exit0 and permitted printed axioms. Command: resource-guarded single-slot lake build GrowRuntime.CallerBudget, SetGrowTail, MemoryModelSetCall, TableRuntime.Budget. Resources {"minimum_disk_available_bytes": 132139565056, "peak_disk_used_percent": 58, "peak_group_rss_kib": 1188, "peak_used_memory_kib": 1458524}. The final cached closure took4.32s; time reported maximum child RSS1,859,600KiB. The sparse guard samples above missed the compiler peak, so their process-group maximum is not a peak compiler-memory measurement. Supporting successful standalone loop/allocation check table-grow-loop-allocations-v2.log1206jobs. Failed development logs were not indexed: AST signed/unsigned mismatch and missing load/assign tags; dependent local-binding conversions and literal-name equalities; missing explicit header values; scope setup conversion timeouts solved by explicit memory equality and a canonical reset state; return empties locals; parser multiline record field; Nat zero-add and projected equality elaboration; finite match arithmetic split by key kind. Final proof uses only permitted axioms.

This is a conditional original-program source-clock/state contract, not target runtime K or full verification. Global reachable heap/array ownership, query/code/domain/clock facts remain explicit. Still open: whole general setter including lookup and growth choice, deletion/truncation, global accounting/rollback/query progress and compiler/target transport. User-facing whole-plan estimate30% (rough25–40%), based on remaining proof obligations, not file counts; no whole-program finite bound yet. Baseline unchanged, claim infinity. Latest account read9%,0 reset credits.


### 2026-10-17: complete original setter and reusable physical postcondition

SetModelPost/Tail/Execution/Call/Budget/Heap prove the full actual original htab_set body and ignored-result caller for all five widths. Lookup, present update, absent insert, exact growth guard, optional actual grow, final raw insert, return/scopes are derived. Postcondition includes exact nonlocal state frame, old/new layout and heap choice, count[D,D+1], all physical table invariants, preservation of half load, actual growth threshold, next power/minimum and current pools below the actual returned heap cursor. If the layout stays old, paid<=noGrowthPrice+1; this avoids charging a quadratic growth price on every call. Full worst allowances: clearPrice(2C)+triangle(D)+19D+19 /28D+34 /15D+17 /27D+23 /40D+46 for20/28/32/52/60. Growth_count_bound ties new capacity to population rather than an unrelated address maximum.

Successful final closure table-set-model-heap-v1.log1300jobs, explicit exit0, permitted printed axioms. Supporting successful table-set-model-tail-v2.log1233, table-set-model-execution-v1.log1234, table-set-model-call-v2.log1235, table-set-model-refined-v1.log1236, table-set-model-budget-v1.log1290; only the final unchanged-source log is indexed. First tail attempt failed because omega did not unfold the p.capacity alias; an explicit bounded fact resolves it. No failed log indexed. Code/query/domain/little-endian/power/clock reachability, potential growth allocation room and global ownership remain explicit. No whole K or verification.

Next: original htab_del physical backshift/order-removal model, htab_truncate, item/slot/keys/copy APIs, then global event/ownership/gas/rollback/query and compiler/target transport. Runtime-only occupancy intentionally does not assert logical NoGaps. In particular, do not assume truncate deletion makes progress merely from binary occupancy: either derive self-lookup reachability or prove that a no-change absent deletion cannot occur on a normally terminating truncate run. Source divergence/timeout is outside the covered terminating scope; any conditional argument must be connected to actual semantics. This is an open proof obligation, not an assumed progress fact.

Important reachability limit: the complete constructive setter contract currently assumes prospective five-array growth room even on an update path. Do not infer that all covered callers have that room. Near the heap end, a present-key update may terminate without enough room for unused growth. Global integration must select an update/no-growth contract, or invert the actual covered normal execution and derive allocation room only when growth is taken. The current source-clock contracts do not discharge this condition.


### 2026-10-18: original deletion moving-hole components

DeleteProgram shape checks the exact original AST, including Boolean wrappers for unsigned movement tests. DeleteSlots/Pending/Initial stage the removed ordinal with a proof-only out-of-range sentinel and track the actual used set as remaining active ordinals plus the moving hole. DeleteMoveMemory/Reads/Stores/Execution derive actual memcpy, old value/inverse-position reads, all three stores, hole assignment and moved_pos restoration, while preserving the pending invariant and physical header. DeleteDecision checks the original comparison/OR/AND tree for all word values; DeleteAfterHash composes home/movable scopes and both decision paths, outputting the old hole or the actual scanned slot. Paid after hashing<=copyPrice(keySize)+1; no-move pays0. DeleteFinalSlots proves the original final last-entry swap map is injective, covers exactly nonremoved ordinals, has length D-1 and yields correct get values. This map is not yet connected to the actual final stores. The sentinel changes only proof data. No source/ROM/semantics/Solution/claim change.

Final successful closure table-delete-after-hash-v2.log1193jobs, explicit exit0 and permitted printed axioms, includes DeleteFinalSlots. Supporting successful targeted logs: table-delete-slots-v1.log1149, table-delete-pending-v1.log1152, table-delete-move-memory-v1.log1163, table-delete-move-reads-v1.log1166, table-delete-move-stores-v2.log1165, table-delete-move-execution-v1.log1168, table-delete-components-v1.log1192. Only final current-source successful log indexed. Development failures: update_self lemma name, if-True reduction, scoped is a reserved identifier, plain simp_all recursion through a retained binding equation, explicit BitVec order/bitwise reductions and literal all-ones fold, let aliases in scope targets/Fin witnesses. Corrected without holes; no failed log indexed.

Next: actual htab_hash caller continuation, masked j scan and first-empty bound with read-only used snapshot; final used-byte clear/last-entry swap/count decrement and full physical post-model; full deletion ABI; truncate progress and other mutable APIs/global accounting. The frontier must prove the current j differs from the hole: the hole is initial i or a prior scanned slot, and the occupied prefix ends before any masked repeat. Do not assume this solely from Pending. Existing first_empty over the original occupied list bounds the unchanged used snapshot; every move preserves used bytes. Latest account read10%,0 reset credits. No whole-program finite K or full verification.


### 2026-10-18: complete original deletion scan

DeleteHashExecution now derives the actual hash call and all h/home/movable scopes, preserving the used-byte snapshot. DeleteScanReads checks the literal masked increment and actual empty-byte test; ScanFrontier derives the first empty within the old occupied count and proves a new scan slot differs from the moving hole before any masked repeat. ScanLocals transports actual saved parameters. ScanStep composes increment, real used read, hash, decision and optional complete move. ScanEnd checks the final increment/break and the enclosing while clock. ScanLoop composes the entire literal while with its physical pending/header invariant, untouched used snapshot, nonlocal frame and all locals except i/j. ScanModel initializes from the actual original Occupied model: at most D-1 occupied successors and one empty iteration, price `(hashPrice+copyPrice+2)*(D-1)+1`. Per-width occupied-iteration coefficients9/17/7/13/25. No logical map/self-lookup correctness assumption is used. Entry code/domain/endian/capacity power/ownership/clocks remain explicit. This is not the complete deletion suffix/caller or global/target K.

Successful final current-source closure table-delete-scan-model-v1.log1333jobs, explicit exit0 and allowed printed axioms; includes DeleteFinalSlots and SetModelHeap. Supporting successful logs hash-execution-v1 (superseded after used-frame strengthening), hash-stable-v1, scan-reads-v2, scan-step-v3, scan-end incorporated in scan-loop-v4. Development failures were syntax/type-class and opaque normalization issues, including UInt8.size vs256, evalHOLFinite vs evalHOLExact in an ite, mixed unfolded scanPrice products in omega, and final literal/let reductions. Corrected proofs have no holes; failed logs are unindexed. Latest account usage11%,0 manual reset credits. Resource snapshot host~1.4GiB used, disk58%; no full verifier. Baseline program/semantics/ROM/fixed proofs/Solution/claim unchanged.

Whole corrected task estimate remains about30%, rough25-40%, based on remaining obligations rather than module count. Witness/later-query aggregation, global reachable input/gas/state/journal/rollback/heap/trie accounting, all-outcome phase composition and unchanged target execution transport remain substantial open work. Next: final used clear/swap/count stores and full deletion caller, then remaining APIs/global integration.


### 2026-10-18: original deletion final mutation and scan composition

FinishMemory defines exactly the original clear/optional two metadata stores/count store, derives all cross-pool frames and distinct store destinations. FinishFields proves the actual used-byte projection (all neighboring bytes retained), unchanged header words and count D-1. FinishArrays proves final order and inverse-position effects for the checked surviving-ordinal map. FinishModel derives complete Occupied with D-1 entries. LastSwap and LastDecision execute the real last_slot declaration, two stores, restoration and optional comparison; last-slot mapping/read requirements apply only on the taken branch. FinishExecution executes the entire actual afterLoop suffix: clear, count read, natural/word decrement agreement, optional swap, count store, return and scopes; establishes the physical model from executed memory. ScanFinish composes this with the complete actual masked scan, preserving the exact nonlocal frame and population bound. No extra source clocks for the final straight-line suffix; those are NOT zero target work. Combined allowance remains `(hashPrice+copyPrice+2)*(D-1)+1`, D>0. Full lookup/header/removed-ordinal/J setup and caller ABI remain next, along with other APIs/global reachability, gas and target accounting.

Successful final current-source closure table-delete-scan-finish-v1.log1209jobs, explicit exit0, permitted axioms. Supporting targeted logs finish-memory-v2, finish-fields-v2, finish-arrays-v2, finish-model-v2, last-decision-v1 and finish-execution-v1 succeeded; only final current-source closure indexed. Development failures were orientation/explicit size normalization, local let unfolding, dependent Fin rewrite motives and multiline record field parentheses. Fixed without holes/new trusted declarations. Baseline source/semantics/ROM/fixed proofs/Solution/claim unchanged; infinity remains and no full verification or finite whole-program K. Account latest11%,0 manual reset credits.


### 2026-10-18: complete original deletion body and caller

DeleteHeader derives all seven actual header loads and local/scope frames. DeletePresent derives the real inverse-position/deleted_pos read, j initialization and all nine scopes around the complete scan/final mutation. DeleteModelTail executes the actual cap read and absent/present branch, choosing a real ordinal from the physical occupied covering list. DeleteModelExecution composes the actual generic htab_find_slot caller and derives every selection premise. DeleteEnvironment/ModelCall execute the unchanged ignored-result ABI used by the guest, returning the physical post-model with count unchanged or reduced by one, unchanged layout/nonlocal fields and preserved half-capacity occupancy. DeleteModelBudget checks exact source-clock caller allowances: for D>0,17D-5/26D-6/13D-3/25D-9/38D-10 at20/28/32/52/60bytes; at D=0,4/11/4/4/15. The suffix bound retains D-1 occupied successor iterations rather than charging D. No logical key equality, hash distribution or self-lookup success assumed. Query/table/code/domain/endian/power/clock reachability remain explicit; no whole target runtime or finite K.

Successful final current-source closure table-delete-complete-v1.log1349jobs, explicit exit0, permitted printed axioms; includes SetModelHeap closure. All development checks in this tranche (header-v1,present-v1,model-tail-v1,model-execution-v1) succeeded; final closure alone indexed. Baseline program/semantics/ROM/fixed proofs/Solution/claim unchanged. Next remaining APIs: truncate progress, slot/item/keys and both copy allocation modes; later global ownership frames, actual gas/journal/rollback/heap/trie accounting and target transport. Account last11%,0 reset credits; host~1.4GiB used and disk58%. No full verification. User reiterated no stop points after a status reply ended the prior turn; continue work when answering progress questions in commentary.


### 2026-10-18: original slot/item bodies and tuple callers

MemoryModelReads derives arbitrary actual table-header evaluations from physical owned header cells. SlotProgram/Execution checks the exact htab_slot AST, real used-byte/header/value loads, stride arithmetic and tuple return with every local scope. Occupied representation derives used0or1; no body clock, actual scoped caller1. ReadCallEnvironment shares the actual two-scalar ABI for differing original formal names/return shapes. SlotTailCall proves the true tail form used by ItemProgram/Execution. Actual htab_item derives its dense order read, in-range slot and real tail call; a valid ordinal returns used1, actual pointer/value and a pure nonlocal frame. ItemCall includes both caller clocks (2total). Explicit owned/header/occupied/index/ordinal/code/domain/clock facts remain; no key-equality assumption or whole-runtime result. Query value cells have only the source word constructor, so typed values are derived rather than assumed.

Final current-source table-item-call-v1.log1182jobs succeeded, explicit exit0/permitted printed axioms. Supporting slot-call-v1 succeeded; slot-execution-v1 failed only because an inferred existential target was prematurely chosen by a reflexive nonlocal-frame goal; corrected by naming its actual restored target. No failed log indexed. Baseline unchanged; infinity/no full verification. Remaining table APIs include truncate/key enumeration/persistent copy. Read-only original-source call search finds htab_copy_scratch only at its definition; defer runtime proof pending exact call-graph reachability rather than requiring an unused helper. Persistent htab_copy is used in commit storage, and truncate in child rollback, so their proofs remain required.


### 2026-10-18: complete original htab_keys enumeration and allocation

MemoryRegion derives ordinary mapped backing words, exact byte addresses and memcpy untouched-word frames for aligned natural intervals. MemoryModelPoolFrame transports the complete physical header/occupied model through writers outside all six pools. KeysProgram checks the exact unchanged AST. KeysGeometry derives padded-stride source/destination ownership and source-table copy frames. KeysLocals/Step derive real signed comparison, dense-order read, actual memcpy and both i/k increments; every copy preserves all table pools and every outside-output word. KeysLoop composes the entire original signed scan. KeysAfterOutput derives header/counter setup and tuple return. KeysAllocation proves exact word-aligned reservation stride*D+8 and actual next heap word. KeysExecution/Call compose alloc, all scopes and real pair ABI. Caller prices5D+2/6D+2/6D+2/9D+2/10D+2 for20/28/32/52/60bytes, D=0included. Output layout, heap cursor/global update, source table and outside reservation frames are checked; no logical key enumeration or source/target equivalence assumption. Entry heap room, prior pool ownership, physical table/code/domain/clock reachability remain explicit.

Successful final current-source table-keys-complete-v1.log1370jobs, explicit exit0 and allowed printed axioms; includes full original setter/deletion closures. Supporting geometry-v1,locals-v2,step-v1,loop-v1,after-output-v1,allocation-v1 succeeded. Failed region-v1 needed record projection normalization; locals-v1 used a field name that shadowed the natural index in a later field; execution-v1 prematurely changed a subtraction-normalization goal. Corrected without holes/new trusted declarations; no failed log indexed. Source-clock accounting omits straight-line work; no whole-program finite K/full verification. Baseline remains unchanged. Account latest12%,0 reset credits.

Next truncate route: use covered normal termination to exclude an absent/no-change self-deletion, instead of imposing unproved logical NoGaps/self-lookup success on the physical model. A normal run cannot take a loop iteration that changes only its clock and returns to the identical program state: finite evaluator add-clock equality would make its final clock equal itself plus a positive number. The exact finite theorem is Flapjack.panPropsEvaluateAddClockEq in Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq. Combine the checked actual delete caller with an exact no-change body frame and this stutter contradiction, then induct on decreasing physical count. This remains future work, not a checked truncate result. Persistent copy and global reachability/gas/journal/heap/trie/target accounting also remain open.


### 2026-10-18: complete original covered-run truncation and telescoping budget

ClockStutter proves that a non-timeout evaluator run cannot produce the identical result/state at a strictly smaller initial clock, using the exact finite Flapjack.panPropsEvaluateAddClockEq. TruncateProgram checks the unchanged AST (the compiler expresses n<count as Cmp.lower n count). Reads/Step derive real count/last-position/order-slot reads, the actual own-key argument and complete original ignored deletion caller with exact scope/state restoration; self-deletion success is not assumed. Stop/Post/Loop show each covered non-timeout active iteration must delete: absence would stutter back to exactly the same tail with less clock and contradict add-clock equality. Count decreases to min(D,n.toNat), preserving the physical table. ClockPadding strips added fuel from an internally funded proof; its funding premise handles extra=0 without an unsound truncated-subtraction inference. TailBound and Execution remove the entry-clock hypothesis and derive actual return0 from any non-timeout body outcome. Input.IgnoredCallNormal inverts the actual successful ignored caller rather than assuming a callee return; TruncateCall includes its outer clock and post-model. Budget proves the telescoping inequality paid+P(min(D,n))<=P(D)+1 and difference bound, with P(D)=a*triangle(D)+b*D, (a,b)=(17,13)/(26,21)/(13,11)/(25,17)/(38,29) at20/28/32/52/60bytes. No charge for retained entries. Physical data/code/domain/endian/power and covered actual-run reachability remain explicit; no unconditional termination or target runtime assertion.

Final current-source table-truncate-complete-v2.log1389jobs succeeded, explicit exit0/permitted printed axioms, with retained KeysCall/SetModelHeap/deletion closures. Supporting stutter-v2,step-v2,loop-v2 (older specific normal version),tail-bound-v2,execution-v2 andcall-v1 succeeded. Corrected development failures: missing reader-ABI import, exact AST reverse unsigned comparison, numeral normalization for BitVec modulo, constructor-disjoint result proof, general-result stopped branch, zero-min lemma spelling, and semicolon parsing in an auxiliary price monotonicity proof. No failed log indexed. All baseline program/semantics/ROM/fixed proofs/Solution/claim unchanged; infinity/no full verification/finite whole-program K. Account latest13%,0 reset credits; host~1.4GiB used/disk58%.

Next: actual persistent table copy (the original uses it in commit_storage). It needs a copied-word/byte content lemma for the real general memcpy, beyond the existing untouched-memory frames; then clone Header/Occupied and actual six-allocation/copy/store body/caller. Scratch-copy has no source call sites and remains deferred to exact call-graph reachability. Global memory ownership frames, actual gas/state/journal/rollback/heap/trie event accounting, whole weighted work and unchanged compiler/target transport still remain open. Continue without stopping after updates.

### Original aligned-copy contents (2026-10-18)

Seven new checked modules prove exact contents of actual memcpy word blocks and both aligned word loops, and the four-byte used-array path using byte projections that preserve neighboring lanes. Combined used-byte transfer covers capacity4 or multiples of8. No oracle, source change or replacement algorithm. Final copy-used-contents-v1.log completed1132jobs, explicit exit0; all printed axioms permitted. Full htab_copy execution/caller/clone model and global entry reachability remain open; these lemmas do not establish whole-program K. Evidence index4723modules/7895facts; inventory4736modules/replacementclosure0/frozenunchanged; incremental policy61605entries/2254075662bytes, infinity (not full verification). Host used1.4GiB, disk58%; account13% used,0 reset credits. Continuing the original plan.

### Complete original persistent clone (2026-10-18)

Original htab_copy body and scalar scoped caller now derive both header reads, six real allocations/copies, five pointer rewrites, return/scopes, exact freshEnd heap reservation, new Header/Occupied and preserved old model, plus every outside-reservation word frame. Exact body price15+prefixCost(stride*C)+3*prefixCost(8*C)+(if C=4 then4 else prefixCost C), prefixCost n=n/32+n%32/8; caller+1. Capacity4 caller26/27/27/30/31 across original key widths20/28/32/52/60. Successful table-copy-call-v1.log1222jobs, explicit exit0, permitted axioms; MaxRSS1849676KiB. Entry ownership/heap room/table/code/domain/little/capacity shape/clock still need global reachability. No full verification or whole-program finite K; infinity unchanged. Index4736modules/7947facts; inventory4749modules/replacementclosure0/frozenunchanged; incremental policy61618entries/2254154274bytes. Continuing original global integration; no stop point.

### Original setter ownership and static copy call sites (2026-10-18)

Added TableFootprint outside-cell/frame predicates, insertion/update/setter effects and disjoint-reader pool transfer. Actual no-growth setter and full growth setup/rehash/body/caller now export full footprints. Carried them through full Set.ModelPost/body/caller and added protected-word and disjoint-table model preservation. Entry ownership/room/code/clock remain conditional; no global MSG reachability or whole runtime bound asserted. Final table-set-ownership-v1.log1296jobs, explicit exit0, permitted axioms, MaxRSS1854792KiB. Static traversal of exact original source declarations (including call handlers) proves scratch-copy no incoming calls and persistent clone only in compute_state_root. original-table-call-sites-v5.log3017jobs, explicit exit0, permitted axioms, MaxRSS7770688KiB. The source AST-to-HOL codec has size-based recursion; computing the static traversal directly on original production syntax with structural recursion avoids reducing large literal sizes. No source or semantics change. Index4740/7962; inventory4753/replacementclosure0/frozenunchanged; policy61622entries/2254169329bytes, infinity. Account14% used,0 reset credits. Continuing remaining deletion/truncation frames and actual global integration.

### Original deletion/truncation ownership (2026-10-18)

Pure actual movable and finish memories preserve every outside-pool word; carried through all decisions/hashes/scan iterations, full deletion/caller ModelPost and covered truncation loop, clock-padding removal, full body/caller ModelPost. Added protected-word and unrelated-table Header/Occupied transfer. No runtime allowance, termination scope or source implementation changed. Successful table-truncate-ownership-v1.log1331jobs, explicit exit0, permitted axioms, MaxRSS1887476KiB. Index4743/7968; inventory4756/replacementclosure0/frozenunchanged; policy61625entries/2254180346bytes, infinity. Global gas/events/ownership reachability, aggregate mutation phase prices and compiler/target K remain open. Continuing, no stop point.

### Aggregate original growth charging (2026-10-18)

Capacity potential P=triangle(C/2)/3+s*C, s7/11/6/9/15 for original widths. Exact triangle doubling identity, monotonicity and clear bound prove full original grow caller allowance<=P(2C)-P(C) under original power>=4 and half occupancy. General actual Set.ModelPost plus checked full/no-growth caller prices imply paid+P(oldC)<=ordinarySetterPrice+P(newC), with a cumulative telescoping theorem. Actual post-capacity<=max(oldC,4*(nextCount+1)). Connected conditional component accounting, not an actual global trace or whole-program K. table-set-amortized-v2.log1297jobs, explicit exit0, permitted axioms. Index4745/7978; inventory4758/replacementclosure0/frozenunchanged; policy61627entries/2254188226bytes, infinity. Continuing actual entry reachability, including deriving allocation room only on branches that allocate.

### Derive reached allocation room and normal original setter bound (2026-10-18)

Eleven new modules: generic no-return leaves/sequence, actual trap_with no normal return even for arbitrary FFI; PersistentAlloc actual normal body/caller inversion and exact natural expected cursor; all5growth allocations and whole grow body/caller normal room/layout inversion; selected setter-tail growth room; full setter normal body, add-clock padding removal, and actual ignored-result normal caller. Conditionalized internal model_tail new-layout premise to the actual absent/threshold branch and exported returned geometry; old constructive API preserved. Successful setter callers now need no prospective growth layout and no entry-clock budget, retaining actual ModelPost/footprint/count/prices/Valid/half occupancy. Existing table/domain/query/code/aligned bounded cursor reachability remains explicit. Final set-normal-call-v1.log1333jobs, explicit exit0, all permitted axioms, MaxRSS1863788KiB; also rechecked SetAmortized closure after internal-tail change. An initial NoReturn experiment used uncontrolled symbolic case splitting; its compiler was terminated before the24GiB host ceiling and replaced with explicit finite splits. That failed log is not evidence. Index4756/7997; inventory4769/replacementclosure0/frozenunchanged; incremental policy61638entries/2254240176bytes, infinity. Host~1.4GiB used/disk58%; account15% used/0 reset credits. Continuing global caller loops and gas/ownership reachability; no full verifier or finite K claimed.

## Original storage-key warming loop — 2026-10-18

- Exact original AST selector and checked local path from the post-MSG_GAS suffix, including preceding address warm-ups and table constructors; normal caller execution yields a real normal loop run.
- Complete actual loop bound, not a supplied mutation trace: counter increment, signed-safe condition, 52-byte key mapping at both alignments, real setter calls, growth allocation room, next table model/heap cursor and protected earlier memory.
- For D initial entries/n remaining keys: paid+P(C0)<= (13D+17)n+13triangle(n)+P(Cfinal). Count in[D,D+n], Cfinal<=max(C0,4(D+n+1)). Constructor/input/global reachability still explicit; no target runtime K.
- Successful root-warm-keys-complete-v1.log, 1363 jobs, exit0, allowed axioms, MaxRSS2093836KiB. Proof index4764modules/8020facts; inventory4777modules, replacement closure0, frozen files unchanged. Local incremental policy check passed; claim infinity. Not full verification.
- Next: derive actual htab_new entry/post states for warm-up loops and carry message/table ownership through the rest of the real root caller.

## Derive original warm-table allocation room — 2026-10-18

- Normal htab_new body/caller derives exact source-clock funding; for word-multiple capacities all six actual allocators derive their total fresh reservation room. Header stores are inverted from actual normal outcomes and the real memzero preserves the heap cursor, without future-layout or mapping oracles.
- Actual process_transaction storage constructor(52,16), i=0 and entire key warm-up now compose from an incoming bounded/aligned heap cursor plus code/input extent. Empty Header/Occupied arrays are established by actual constructor memory. Price10+17n+13triangle(n)+P(Cfinal)-P(16); earlier words preserved. Input extent/global reachability, address warm-ups, subsequent message/root execution, weighted target transport and finite whole-program K remain open.
- Successful root-warm-constructor-normal-v1.log1384jobs, exit0, permitted axioms, MaxRSS1885544KiB. Index4776modules/8042facts; inventory4789modules, replacement closure0, frozen files unchanged. Incremental policy check passed, claim infinity; no full verification.

## Original precompile warm-up prefix — 2026-10-18

- Exact original AA constructor(20,64), sender setter, skips, counter reset and18-address warming loop now compose from actual normal caller execution. Actual counts<=1 then<=19 rule out every growth; caller heap/globals and all words outside the original table pools survive.
- Constructor derives allocation room and empty physical model. Combined source-clock bound1795, no prospective room or clock-budget premise. Preserves every word below the incoming account-table cursor. Sender/precompile mappings and actual global reachability remain entry obligations, as do access-list address warming and all subsequent message/whole-target work.
- Successful root-warm-precompile-constructor-v3.log1386jobs, exit0, permitted axioms, MaxRSS1931560KiB. Index4785modules/8063facts. Incremental inventory/policy passed; frozen source unchanged, claim infinity, no full verification.
- Next active work: access-list address warming with protected actual pointer-array reads and growth. A generic TableState refactor is pending/checking, not evidence yet.

## Complete original transaction table warm-up — 2026-10-18

- Shared generic physical TableState replaces the storage-only duplicate while both retained warm-up proofs still build. Exact protected pointer-array model supplies real access-list query loads and persists through every actual setter/growth.
- Entire AA constructor/sender/precompile/coinbase/access-list prefix joins the actual AK constructor/storage-key loop. Both resulting Header/Occupied models and half/power/heap invariants are retained, arrays naturally separated. All earlier words and unrelated caller locals survive.
- A addresses and S keys: paid+P_account64+P_storage16<=1805+184A+9triangleA+17S+13triangleS+P_accountCa+P_storageCs, with Ca<=max64(4(A+20)), Cs<=max16(4(S+1)). WarmTables.price gives a concrete finite source-clock phase price after substituting those capacities. Entry input/heap/code reachability and source clock/target-work distinction remain explicit.
- Successful root-warm-tables-price-v1.log1404jobs, exit0, allowed axioms. Index4796modules/8083facts; inventory4809modules, replacement closure0, frozen files unchanged. Incremental policy passed; claim infinity; no full verification.
- Continuing with original message allocation/setup and preservation of its actual MSG_GAS through this warm-up stage. Later destination setup/helpers/final AA setter/message execution, global gas, weighted target transport and whole-program finite K remain open.

## Original persistent message constructor — 2026-10-18

- Actual msg_new allocator and full176byte clear derive reservation room and returned pointer,9body/10caller source clocks, real normal continuation/scopes and all cleared words. Outside-allocation memory is preserved. No entry-clock or prospective-room premise.
- Successful message-new-call-v2.log1161jobs, exit0, allowed axioms, MaxRSS1860576KiB. Index4800modules/8091facts; inventory4813modules, frozen files unchanged/replacement closure0; incremental policy passed; claim infinity.
- Continuing with caller message stores and physical MSG_GAS preservation through the checked warm tables. Source heap/domain/code entry reachability and all later root/message/global/target work remain open.

## Message initialization, warm tables and actual validator gas — 2026-10-18

- Complete original msg_new, all7message stores and both complete warm-table phases now compose through actual m/aa/ak scopes. Region/message placement, exact MSG_GAS word, both table models, pointer arrays, source clocks and earlier-memory frames are conclusions. Phase bound10+WarmTables.price(A,S); no future-room or entry-clock allowance.
- Actual post-gas reservoir and four-word value stores preserve gas/input words by executed read widths and mapped write lists. Diagnostic AST comparison caught global be versus an incorrect local proof expression; corrected to unchanged original global read, then the exact selector/path passed.
- New paired-local path supplies one actual allocation state retaining both gas/reservoir words. The unchanged validator/root split derive the gas cap at this state, with no intrinsic/gas/helper/clock oracle. Input/heap/body-binding reachability remains explicit; this has not proved the caller preprocessing price or whole root/message execution.
- Successful combined root-message-validated-v1.log1421jobs, exit0, allowed axioms, MaxRSS2099260KiB; includes root-message-initialized-v2 closure. Index4813modules/8113facts; inventory4826modules, frozen files unchanged/replacement closure0. Incremental policy passed; claim infinity; no full verification.
- Continuing into remaining original recipient/create setup, final AA setter and process_message_call/frame gas coupling, while preserving explicit upstream input/heap obligations. Whole-program gas/event/phase counts, arbitrary input reachability and weighted target K remain open.

## Full original non-creation root setup — 2026-10-18

- The exact original recipient branch, all6field stores, reached8byte empty allocation, final AA setter and final2table-pointer stores now reach the actual process_message_call declaration with preserved gas and both physical table models. Per-pool disjointness survives relocation across the other live table; copied transaction fields are protected by the earlier owned400byte record.
- Composed with actual msg_new/all7initial stores/all warm tables through real m/aa/ak/empty scopes. noncreatePrice(A,S) combines source-clock charges, telescoping actual growth potentials and capacity/population high-water bounds. No entry-clock or future-room allowance; actual input/heap/query/code reachability is explicit. Creation path and subsequent message/global/target proof remain open.
- Successful root-recipient-noncreate-v1.log1433jobs, exit0, allowed axioms. Evidence index4827modules/8150facts; inventory4840modules, frozen files unchanged/replacement closure0. Incremental policy passed61709entries/2254552607bytes; claim infinity. No full verification or whole-program finite K.

## Original message-call prefix and active frame entry — 2026-10-18

- Actual process_message_call output alloc96/clear96 derives reached room,5source clocks, exact cleared state and preservation of all earlier words/live tables. The exact root call site is checked against the pinned AST.
- Original frame_open body and scoped caller derive their clock payments from actual normal runs with temporary padding removed. They retain canonical child/continuation activation and initialize the active child's regularBudget from physical MSG_GAS. Actual process_message depth guard/parent scopes reach this call and retain actual continuation/restoration; no helper-return or entry-clock oracle.
- Empty-code root message region plus live AA/AK headers now derive all frame input mappings, physical table counts and separation from the arena; no code-buffer mapping is needed at length0. Arena/code/global/cursor/room reachability remains explicit. Actual root stores/setters additionally retain exact reservoir/code/length fields.
- Successful root-frame-input-fields-v1.log1504jobs, exit0, permitted axioms, MaxRSS2723952KiB. Index4837modules/8168facts; inventory4850modules, frozen files unchanged/replacement closure0. Incremental policy passed61719entries/2254594004bytes; infinity, no full verification/whole-program finite K.
- Continuing with original message dispatch, source/active-frame gas coupling and reachable arena/dataflow conditions. Creation and global gas/event/phase counts, input/parser failure paths and weighted target transport remain substantial open work.

## Actual root call to the active capped regular ledger — 2026-10-18

- Scalar store normal inversion derives actual mappings/effects. Source transaction field152 now copies into MSG field24 through its exact first store, and survives MSG_GAS, all remaining stores/warming and recipient initialization. The full root helper exports this exact word from protected TxData.
- Actual process_message_call non-creation dispatch executes the assigned process_message call. That real callee's depth guard, parent scopes and full frame_open reach the actual active child; helper results/traces/clock funding are conclusions. Output alloc96/clear96 preserves old message/count reads by owned interval/header bounds.
- Body prefix bound is length+memzero_price(bitmapBytes(length))+51source clocks; actual root caller adds1. Empty-code allowance53. The physical MSG_GAS cell supplies the active regularBudget and its validated intrinsic-adjusted cap. Arena/code/cursor/input ownership/room remain explicit; downstream preparation/frame loop/creation/global counts and target K remain open.
- Successful message-call-normal-open-v1.log1511jobs, exit0, permitted axioms, MaxRSS1935504KiB. Index4844modules/8178facts; inventory4857modules, frozen files unchanged/replacement closure0. Incremental policy passed61726entries/2254626571bytes; claim infinity, no full verification or whole-program finite K.

## Combined actual root setup through active child — 2026-10-18

- HeapGlobals preserves every original non-heap binding through actual setter/growth posts, both full warm loops/constructors, message stores and recipient setup. Initial arena/parent/continuation/empty globals now transport to the real call entry instead of becoming new intermediate assumptions.
- NoncreateSetup/FrameCode/ArenaEntry list outstanding source entry reachability explicitly. From these and the real normal root run, active_noncreate_normal derives complete setup/message dispatch/activation at price noncreatePrice(A,S)+53source clocks. Physical MSG_GAS initializes the exact capped active regular ledger.
- Both AA/AK models survive output allocation/clear and every frame/stack/bitmap/list/table/continuation allocation. The actual advanced persistent heap cursor is derived and shared by both surviving models; code/domain/endian and active global bindings also transport.
- Successful root-active-frame-v1.log1515jobs, exit0, permitted axioms, MaxRSS1966668KiB. Index4848modules/8184facts; inventory4861modules, frozen files unchanged/replacement closure0. Incremental policy passed61730entries/2254648487bytes; infinity, no full verification/whole-program finite K.
- Continuing past active opening into depth0 preparation/frame start/run loop and global gas/state accounting, while source input/code/arena reachability, creation and weighted target transport remain open.

## Actual normal regular/state/refund/refill transitions — 2026-10-18

- Normal scalar operation/load/store inversion derives actual nonempty write mappings. A real charge_gas derives both frame-cell words/maps and affordability; its capped physical ledger implies non-wrap, exact natural debit/used credit and strict counter progress for positive amounts. Caller funding is derived, exact1source clock.
- Full original add_sat arithmetic now supplies min(maxWord,naturalSum) and coverage even on overflow. Retained its existing execute/call/ge_left/value_fee_lower API and checked ValueFee. Actual normal charge_state_gas guards derive affordability without exception shape, sum-fit or funding assumptions; temporary padding then gives the real1or2caller clocks, exact pool writes and preserved regular ledger.
- Actual refund/refill normal callers derive their exact2/1clocks, full caller frames and preserved capped regular ledger. Current owned message/frame mappings and words remain explicit; no helper result or ledger result is assumed.
- Successful gas-normal-transitions-v2.log1592jobs, exit0, permitted axioms, MaxRSS1855800KiB. Index4858modules/8205facts; inventory4871modules, frozen files unchanged/replacement closure0. Incremental policy passed61740entries/2254690801bytes; infinity, no full verification/whole-program finite K.
- Continuing with original frame exception/exit paths and global frame-loop progress. Depth0 preparation, all-opcode/child/rollback ownership, event counts, input/startup/arena reachability and weighted target K remain open.

## Actual frame exception and done marker — 2026-10-18

- Actual frame_halt caller derives its single clock and non-wrap from the capped regular ledger, with exact used/liquid/error writes, preserved budget and zero liquid gas.
- Exact original frame_exception AST and both branches now compose actual refill, optional halt, return-data/direct-error stores, final continuation+32 done store and return. Full body and caller derive1or2/2or3source clocks, preserve the regular ledger and mark the real continuation done. Nonmemory state/caller locals are framed; no successful-helper or entry-clock premise.
- Current frame/message mappings/words, source code and continuation separation remain explicit. The done-marker/run_frames exit connection, opcode/child/rollback ownership/progress and global event counts remain open, along with creation/input/startup/arena reachability and target K.
- Successful frame-exception-normal-call-v1.log1598jobs, exit0, permitted axioms, MaxRSS1827404KiB. Index4864modules/8216facts; inventory4877modules, frozen files unchanged/replacement closure0. Incremental policy passed61746entries/2254716861bytes; infinity, no full verification/whole-program finite K.

## Live table family and original journal rollback prerequisites — 2026-10-18

- TableFamily tracks arbitrary live table identities, all physical models, pairwise pool separation and a common actual heap cursor. Actual original set/delete calls retain every model and stable header pointer; deletion derives its clock allowance from the actual normal call. Set growth derives reached room and charges its existing amortized potential.
- SetEarlierFootprint preserves earlier words outside old pools even when the protected object lies between pools. JournalImage records the actual four-word entries and mapped copied queries, separated from every live table. Both executed mutation helpers preserve the complete image and every reader; no logical dictionary correctness or favorable collisions are assumed.
- Checked exact state_restore body, real unsigned guard, non-wrapping decrement, preserved family under journal_n assignment, and actual three-declaration record entry with lexical restoration. LocalPrefix gained a globalAssign constructor with its checked caller-local summary.
- Successful journal-counter-family-v2.log1435jobs and journal-records-mutations-v3.log1439jobs, exit0, permitted axioms; latest MaxRSS1910612KiB. Failed attempts concerned missing imports/namespace qualifications and restoration simplification; only successful final logs indexed. Index4877modules/8242facts; inventory4890modules, frozen files unchanged/replacement closure0. Incremental policy passed61759entries/2254766783bytes; claim infinity.
- Actual branch/loop composition, journal init/append/snapshot reachability and global rollback/event counts remain open, together with all other whole-program ownership/progress and weighted target obligations. No finite whole-program K or full verification claimed. Continuing without a milestone stop.

## Complete original rollback loop, body, caller and snapshot — 2026-10-18

- FamilyPotential sums growth potential over the finite live family; one writer update lifts to the whole-family amortized inequality, permitting rollback writers to alternate. Actual record flag and argument loads select the real helper. Each complete loop body preserves unread records/all table models and decreases the unsigned counter without wrap.
- Actual while evaluation derives n=count-snap iterations and telescopes paid+P(entry)<= (38D+40)*n+38*triangle(n)+P(exit), for population bound D. The complete zero-return body and real ignored-result caller are checked; caller adds1. An already-restored later snapshot takes no iterations and preserves all state except one caller clock. Final journal_n=min(count,snap). Canonical code, actual family/image and extent remain entry obligations.
- Exact original state_snapshot body/caller stores the actual journal_n in its scoped local, derives the one caller clock from enclosing normal execution and retains all other state. Empty journal images are established without initialized record contents.
- Successful journal-snapshot-restore-v2.log1522jobs, exit0, permitted axioms, MaxRSS1977732KiB. Earlier failures were local alias normalization/evaluator presentation and over-simplification of a tuple; only final successful logs indexed. Index4887modules/8265facts; inventory4900modules, baseline unchanged/replacement closure0. Incremental policy passed61769entries/2254814589bytes; claim infinity, no full verification.
- Continuing into actual journal append/guard/initialization reachability, then global rollback counts and frame exit composition. Whole-program input/startup/creation/gas/ownership/weighted target obligations remain substantial; no finite K or completion claimed.

## Actual append guard and copied-key prefix — 2026-10-18

- Current physical table ownership now derives all original htab_get reads and values. Actual normal body/caller evaluation yields the binary flag/stored word, collision-sensitive price and full nonlocal read-only frame; no entry-clock budget remains. This carries actual journal_n/journal_cap through the initial append lookup.
- Exact jset/jdel ASTs and actual overflow guards are checked. Normal jset passes the guard; jdel either returns0 without appending on its real absent-key branch or passes the guard. Actual trap4/5 cannot continue normally, with arbitrary trap FFI effects still allowed on failing paths.
- Zone owns all fixed journal slots, including currently unused slots; their physical maps follow from ordinary region bounds. Exact shared key prefix reads actual table key length, derives normal allocator room and rounded cursor, executes real memcpy with derived clock funding and reaches the real record-store suffix with lexical restoration intact.
- Key prefix cost<=keySize+2source clocks. Its fresh copy preserves all old words, complete live table family and journal image; the actual heap cursor advances by stride(kind), and nonheap globals survive. FamilyMemoryFrame supplies actual cursor advancement and old-pool preservation.
- Successful journal-key-model-v2.log1538jobs, exit0, permitted axioms, MaxRSS1978972KiB. Failed attempts involved explicit structure projection normalization, target inference and a missing classical instance; no failed logs indexed. Index4899modules/8291facts; inventory4912modules, frozen baseline unchanged/replacement closure0. Claim infinity; no full verification or finite whole-program K.
- Continuing with four journal record stores/counter increment/final mutation, complete append caller ownership, initialization and global counts. Existing whole-program creation/input/startup/arena/gas/phase and weighted target obligations remain open; no milestone stop.

## Complete original jset body and caller — 2026-10-18

- Journal word geometry is injective across all slots/fields. Four actual record writes establish the extended image and preserve all old records and table pools. Both original store ASTs, real tuple/local reads and lexical record declarations are checked. Actual cap-guard room implies the real unsigned journal counter increment does not wrap.
- Arbitrary final setters preserve the complete journal reservation, including unused slots, and live image across reached table growth. The actual original increment/set/return tail and all post-copy record scopes compose on their normal execution.
- Complete jset body/caller now derives the saved old flag/value, copied-key pointer, new journal_n=count+1, next image, all table models and unused-slot ownership from actual getter/guard/key/store/increment/set execution. Caller paid+P(old)<=Get.bodyPrice(kind,D)+1+(keySize(kind)+2)+Set.noGrowthPrice(kind,D)+2+P(new), with binary actual old flag. Caller locals and noncontrol globals survive. No intermediate helper runs/models, source-clock allowance or future-room assumptions.
- Successful journal-jset-call-v1.log1550jobs, exit0, permitted axioms, MaxRSS1962932KiB. Index4911modules/8319facts; inventory4924modules, frozen baseline unchanged/replacement closure0. Incremental policy passed61793entries/2254921049bytes; claim infinity. No whole-program finite K or full verification.
- Continuing with complete jdel, journal initialization and global append/rollback accounting, then frame exit composition. Other whole-program input/startup/arena/creation/gas/phase/weighted target obligations remain open; no milestone stop.

## Complete original jdel body and caller — 2026-10-18

- Generic actual deletion retains the full fixed journal reservation as well as its live image. Exact original jdel record declaration, four stores with literal flag1, increment, real deletion and zero return compose with original-query arguments. Key allocation/copy preserves current table plans/counts and old records; deletion keeps plans/capacities and never increases population.
- Complete original body/caller covers actual absent/present getter outcomes. Absent caller is exactly the original source state with only its paid clock changed, cost<=Get.bodyPrice(kind,D)+2. Present caller costs<=Get.bodyPrice(kind,D)+1+keySize(kind)+2+Delete.modelPrice(kind,D)+1+1, appends its actual old value/literal1 and copied-key pointer, sets journal_n=count+1 and advances the persistent cursor by stride(kind).
- All present-path family/image/unused-slot models survive, along with caller locals and noncontrol globals. Source ownership/code/mappings/global bindings remain entry obligations; actual normal execution derives helper paths, funding and future allocation room.
- Successful journal-jdel-call-v1.log1556jobs, exit0, permitted axioms, MaxRSS1971144KiB, also checks current jset caller. Index4917modules/8325facts; inventory4930modules, frozen baseline unchanged/replacement closure0. Claim infinity, no whole-program finite K/full verification.
- Next strengthen existing rollback contracts to preserve the full unused reservation, so the actual append/restore ownership cycle closes. Current rollback retained only the live image; that suffices for its local loop but not for a later append. Then continue journal initialization, global append/rollback counts and frame exit composition; remaining whole-program obligations stay open.

## Retain unused reservation through actual rollback — 2026-10-18

- Strengthened actual selected mutation/record/body/loop/return/caller rollback contracts to retain Zone for every unused slot, using the generic original set/delete reservation frames. Replaced the separate live-prefix extent premise by the current owned reservation and count<=cap. Both full-image and no-op snapshot cases retain the reservation. The existing amortized price and actual unsigned iteration count are unchanged.
- Subsequent appends can now consume the post-restore family/image/unused-slot facts directly. The interface remains conditional on source physical ownership/code/current counter; this does not establish whole-program state reachability or a global event count.
- Successful journal-restore-reservation-v1.log1554jobs, exit0, permitted axioms, MaxRSS2009564KiB, elapsed1m20s. Checks strengthened rollback, snapshot and both original append callers. Index4917modules/8325facts; inventory4930modules, frozen baseline unchanged/replacement closure0. Incremental policy passed61799entries/2254961202bytes; claim infinity; no full verification or finite whole-program K.
- Continuing with original initialization of journal cap/backing region/zero counter, then actual table-family extensions and global count coupling. Other whole-program ownership/gas/input/creation/phase/weighted target obligations remain open.

## Original journal initialization and fresh identity extension — 2026-10-18

- Exact state_init suffix selects the original capacity524288 assignment, real global-result16MiB allocation, actual journal_n/ts resets and zero return. Actual normal execution derives allocation room, one call clock and exact complete post-state. Global assigned allocation now has a checked normal/exact-cursor contract; ordinary global assignments derive their complete update without an old-value or shape premise.
- LocalPrefix gained checked globalCall support. The initialized suffix preserves every old table pool/model at the advanced cursor, establishes the complete unused reservation separate from all old pools, and creates an empty journal image with the actual zero counter. Incoming heap geometry/journal binding/allocator code and existing family remain explicit; no future room or initialized record contents are assumed.
- TableFamily.Model.extend adds a genuine fresh identity behind the old pools, while Zone/Image extension retains the entire reservation and lifts old saved identities through Option.some. Actual constructor connections are next; this is not yet complete state_init/state_fresh_tx reachability.
- Successful journal-init-owned-v2.log1563jobs, exit0, permitted axioms, MaxRSS1951288KiB, elapsed11.87s; includes both append callers and strengthened rollback. Failed first initialization attempt involved reversed literal-name inequalities and a missing explicit geometry import; only final successful logs indexed. Index4925modules/8336facts; inventory4938modules, frozen baseline unchanged/replacement closure0. Incremental policy passed61807entries/2254986665bytes; claim infinity; no full verification or finite whole-program K.
- Continuing with actual original constructors/family/record preservation and global append/restore counter accounting, then frame exits and all outstanding whole-program obligations. Source clocks continue to omit straight-line work; weighted target transport remains necessary.

## Complete unchanged transaction-state initialization — 2026-10-18

- Checked exact original state_fresh_tx AST:72-byte record, eight original constructors/capacities, nine pointer stores, actual journal_n reset and return. Scoped first constructor and later assigned local constructors derive all reached allocation room and funding from normal execution. Body81source clocks, real ignored caller82; persistent cursor advances17176bytes.
- Added constructor family extension and word-region separation for records between earlier/later pools. Every old table retains its identity/physical model; all eight new empty tables are modeled, and actual transaction-record fields hold their pointers. The block-state pointer survives, caller locals/code survive, and the complete journal reservation remains protected with the actual zero counter and empty image. Entry family/zone/current heap/bs/ts bindings/installed code remain explicit; this is not whole-program reachability or target runtime K.
- Removed an unused new journal-word helper and unused assumptions/imports. No guest implementation, semantics, ROM, fixed proofs, Solution or claim changes. Cleanup of the replacement program remains completed as previously recorded.
- Successful state-fresh-tx-call-v2.log1603jobs, exit0, permitted axioms, MaxRSS1987168KiB, elapsed10.17s; also checks journal initialization and both original append callers. Earlier failures were missing imports, explicit record projection arithmetic, a closed-tail unification timeout (fixed by a generic suffix theorem), one recursion-depth failure in code projection (fixed by explicit intermediate equality), and two mistyped optional target names. Failed logs were not indexed.
- Index4940modules/8373facts; inventory4953modules, unchanged baseline/replacement closure0. Incremental policy passed61822entries/2255062736bytes, claim infinity. No full verification or finite whole-program K.
- Continuing with actual journal event-count telescoping, frame rollback/exit composition and global reachability/gas/input/creation/phase/weighted-target obligations. No milestone stop point.

## Actual original frame epilogue — 2026-10-18

- Exact frame_epilogue AST and actual error/snapshot loads select unchanged state_restore. Both branch/body/ignored caller contracts derive helper traces/funding/reached allocation room and retain table family, live image, full unused reservation, caller locals/code and noncontrol globals. Success removes0 journal records; an error removescount−min(count,snapshot), including snapshots beyond the current count. The actual counter satisfies finalCount+removed=initialCount.
- Error body pays at most Journal.price(D,count−snapshot)+1 under whole-family potential accounting; success body0; outer caller adds1. Entry table/journal ownership, code, mapped/stored error/snapshot cells and population remain explicit. This does not yet prove low scratch-memory or regular-ledger preservation, full run_frames progress, global append/restore counts or target K.
- Successful frame-epilogue-call-v1.log1527jobs, exit0, permitted axioms, MaxRSS1955752KiB, elapsed4.90s; prior program/choice/body checks succeeded. Index4945modules/8381facts; inventory4958modules, unchanged baseline/replacement closure0. Incremental policy61827entries/2255081251bytes, infinity claim; no full verification. Host2.9GiB used, disk58%/123GiB free.
- Continue aggregate counter accounting and physical potential bounds, then scratch/ledger frames and all remaining global/weighted obligations.

## Journal conservation and physical aggregate bounds — 2026-10-18

- Added currentCount/CounterEffect on actual state journal words, with conservation for append, restore, unchanged branches and fresh transaction reset/discard. A composable CounterLedger proves total restored<=initial+appended for every accounted prefix. Actual jset, absent/present jdel, state_fresh_tx and all epilogue layers now return the appropriate effect from their checked executions.
- Proved price superadditivity and aggregation: sum(price(D,n_i))<=price(D,sum n_i); the accounted total is bounded by initial+appended. A cumulative amortized inequality can close using the actual final physical family. Whole-program ledger/event extraction, its cumulative inequality, gas coupling and total append counts remain obligations. This is not a global bound from an arbitrarily chosen abstract trace.
- Physical packing injects six actually distinct words per capacity slot from the keys/value/order/position pools across all table identities into the real heap word interval. Thus sum capacities<=648019952; existing half-occupancy/power-of-two facts imply each population<=268435456. Proved24*familyPotential<=sumCapacity^2+360*sumCapacity, hence actual final-family potential<=17497087144886042. No favorable hash or chosen final capacity is assumed. This is one local source-resource term, not K.
- Source inspection confirms many actual heap_mark/heap_release scopes, so no global heap-monotonicity or total-allocation argument was introduced. Current pool ownership is enough for the packing theorem; lifetime and main-path ownership remain explicit. Removed an unused newly drafted lower-prefix helper because its fixed domain threshold did not cover the scratch arena; the next preservation interface should use table lifetime floors.
- Successful journal-aggregate-price-v6.log1707jobs, exit0, permitted axioms, MaxRSS2016844KiB, elapsed12.87s. Final closure includes strengthened actual event callers. Failed attempts involved a redundant tactic, explicit dependent projections/typeclass unfolding, a wrong mathlib tactic import, finite-sum binder scope, triangle rewrite order and a missing explicit summand. Failed logs not indexed.
- Index4949modules/8401facts; inventory4962modules, unchanged baseline/replacement closure0. Incremental policy passed61831entries/2255102325bytes; claim infinity; no full verifier or whole-program finite K.
- Continue rollback preservation of scratch/gas words using a common lifetime floor, then the actual frame exit/child/dispatch progress cycle, remaining initialization/input/creation/global counts and weighted target transport.

## Rollback floor frames and actual child gas merge — 2026-10-18

- FloorFrame carries stable per-table lifetime floors and exact memory preservation for words below all old floors. It composes across writer changes and mutations; a common reachable arena split instantiates it. Original set/delete reservation contracts now retain it, as do selected rollback, record/body/loop, complete restore body/caller, no-op later snapshots and all epilogue layers. Existing append tails consume the stronger mutation outputs without changing their behavior or price.
- Checked regularBudget projection protects actual frame words64/184/192, including from a common cut with frame.toNat+200<=cut. Caller must establish that every table floor lies beyond the scratch/frame arena; no such reachability was assumed from the weaker ordinary-memory lower bound. FloorFrame also protects continuation-record words once that split is supplied.
- Actual child-error incorporation now derives its single caller clock from the normal run and arithmetic no-wrap from the capped combined parent/child regular ledger, retaining the spill-accounting equality and cap. The actual original child-success body reaches its real log/union suffix after spill repayment with exact combined regular budget, without supplied entry clock or sum-fit oracle. Log append/union prices and ownership, full child finishing and run_frames progress remain open.
- Successful journal-floor-frame-v1.log1707jobs, then frame-table-ledger-v1.log1723jobs and final child-success-normal-prefix-v1.log1727jobs; all exit0/allowed axioms. Final incremental closure elapsed4.33s, MaxRSS1810444KiB. Index4953modules/8410facts; inventory4966modules, baseline unchanged/replacement closure0. Incremental policy61835entries/2255116438bytes, claim infinity; no full verification/K. Latest account27% used,0 reset credits; host3.3GiB used/disk58%.
- Continue actual root-exit control after epilogue (using protected continuation words), then child log/union and dispatch/frame progress, along with all outstanding initialization/input/creation/global counts and weighted target transport. No milestone stop point.

## Actual run_frames root-exit control — 2026-10-18

- Selected the actual run_frames completion branch from the unchanged AST, retaining its literal skip, real epilogue call, root-kind test and child alternative. On actual root kind0, the normal execution restores saved ev/cur_cont through genuine continuation-record loads, then sets the real go local0. Destination-shape checks come from the normal assignments.
- Composed the actual epilogue's family/image/unused reservation/counter effect/floor frame with those assignments. The common arena split protects source record fields0/8/16 through rollback; physical regular-budget words survive. No extra source clocks beyond the epilogue, and all current models/journal effect/code/environment are retained. Entry root-kind/mappings, record values, physical models and reachable floors/arena split remain explicit.
- Successful root-exit-normal-v2.log1730jobs, exit0, allowed axioms, MaxRSS1980308KiB, elapsed5.35s; final closure includes all append, initialization, aggregate and child-normal helpers. Initial composition failed only because simplification unfolded the named record-load expression before using its checked read; retained that expression in the read lemma. Failed log not indexed.
- Index4956modules/8415facts; inventory4969modules, unchanged baseline/replacement closure0. Incremental policy61838entries/2255130710bytes, infinity claim; no whole-program K or full verification.
- Continue the surrounding actual run_frames loop and entry scopes for a marked-done root frame, then the dispatch/child cases and outstanding main reachability/gas/input/creation/weighted-target obligations.

## Complete marked-root run_frames body and caller — 2026-10-18

- Exact original run_frames body/loop/head shapes and nonzero continuation done32 path: actual done declaration/assignment selects completion, then real root epilogue/exit and done lexical restoration. ControlResult/sequence/while inversion exposes actual ordinary outcomes and proves that reachable root completion has no escaping return/break/continue. No loop-safety or helper trace is assumed.
- The marked-root while takes exactly one real iteration, clears go through the actual assignments, reads zero and exits. Whole original body includes go declaration, actual final zero return and outer lexical restoration; real ignored caller restores all caller locals. Source clocks: success body2/caller3; error caller bounded by Journal.price(D,count−snapshot)+4 under whole-family potential accounting. Every clock and reached allocation room is derived from normal execution.
- Retains complete physical family/image/reservation, actual min counter/CounterEffect, all table floors/older words and physical regular budget under the explicit arena/floor split. Root-kind/marked word, record maps/cells, incoming ownership/code and split remain entry facts. This is one complete conditional run_frames path, not all opcode/child paths, whole-main reachability or target K.
- Successful run-frames-root-call-v1.log1741jobs, exit0, allowed axioms, MaxRSS1961812KiB, elapsed7.86s. Earlier failed checks concerned an incorrect MlS qualification, expected-type projection unification, subst selecting an earlier projection/equality instead of the intended state/result equation, and unfolding evalHOLFinite in only the read rather than its target. Fixed with explicit projections/rewrites and consistent normalization; failed logs not indexed.
- Index4966modules/8428facts; inventory4979modules, unchanged baseline/replacement closure0. Incremental policy61848entries/2255175570bytes, infinity claim; no whole-program finite K/full verification. Latest account28% used,0 reset credits.
- Continue other immediate root exits (halted frame/pc at code end), actual opcode and child-frame completion/progress, all remaining source entry/input/creation/gas/count obligations, weighted target transport and final cleanup/checks. No milestone stop point.

## All actual immediate root-completion guards — 2026-10-18

- Generalized the checked run_frames root-body/loop/whole-body/caller contracts to ImmediateDone source memory facts: nonzero continuation done, unmarked halted frame, or unmarked running frame with unsigned pc>=codeLength. Existing theorem names marked_root_* are retained but their entry predicate now covers all three actual immediate-completion cases.
- Selected the unchanged halted/pc branches from the real AST. The code-end case reads the actual pc/length, proves the unsigned guard, executes markDone, and restores the pc lexical scope using checked binding laws. Shared body_after_head retains the original done scope. No helper execution or new source-clock allowance is assumed. Existing success3/error Journal.price+4 caller prices and every physical/journal/counter/floor/gas postcondition are retained. Source code/domain/models/root/arena facts remain explicit.
- Successful run-frames-all-immediate-v2.log1742jobs, exit0, allowed axioms, MaxRSS1964292KiB, elapsed16.77s. Earlier local attempts exposed finite-evaluator match/iota normalization and a semireducible state alias during simp; fixed with explicit conditional/state types and exact lexical restoration. Failed logs not indexed.
- Index4967modules/8433facts; inventory4980modules, unchanged baseline/replacement closure0. Incremental policy61849entries/2255185515bytes, infinity claim; no whole-program finite K/full verification.
- Continue the real caught opcode/child calls and their control/ledger effects, then full dispatch/child progress plus outstanding input/initialization/creation/global counts and weighted target transport.

## Whole-loop caught-handler control and actual call cases — 2026-10-18

- Added HandledPrefix as a separate extension of checked LocalPrefix, avoiding an unnecessary rebuild/change to the widely imported base grammar. Actual caught ignored calls may return normally or execute a checked handler; all source states retain the tracked local on continuation and cannot escape through return/break/continue. Exception metadata/shape-check failures remain actual errors.
- Checked the complete unchanged run_frames loop body, including opcode/finish_child EvmErr handlers, against that grammar. A normal-loop inversion now derives the real normal first body/tail and consumed loop clock for every taken iteration, not only root/immediate cases. This establishes no gas rank, iteration-count bound or opcode resource price.
- Actual caught-call inversion separately derives positive caller clock and either the genuine callee return/full caller-local restoration, or genuine matching scalar exception and actual normal handler execution. The original scalar exception-shape lookup is an explicit entry fact. This will connect real opcode/child failures to frame_exception and the gas/control invariant. No supplied helper traces are used.
- Successful caught-call-normal-v3.log1747jobs, exit0, permitted axioms, MaxRSS1806516KiB, elapsed4.58s; includes all current iteration/root/journal/initialization/child helpers. Earlier failures involved a mistakenly shared existential type annotation and a Bool conjunction lemma spelling; corrected explicitly. Failed logs not indexed.
- Index4972modules/8441facts; inventory4985modules, unchanged baseline/replacement closure0. Incremental policy61854entries/2255200794bytes, infinity claim; no whole-program finite K/full verification.
- Continue concrete opcode-dispatch selection/call provenance and gas-or-terminal progress, then child completion/log/union and all remaining main entry/input/creation/count/weighted-target obligations.

## Complete original dispatcher selection and callee provenance — 2026-10-18

- Exact original op_dispatch body is checked equal to a literal guard/action description. Guard evaluation is read-only and handles all64-bit op words; all selected leaves are either the genuine EvmErr5 raise or an original helper call followed by return0. No fallthrough/direct-success leaf is reachable. This describes the original implementation and does not replace it.
- Actual normal/exception inversion derives selected helper arguments/code/callee execution, caller funding and full local/state restoration. Normal dispatch returns0; exceptional dispatch either performs the direct invalid-opcode raise or propagates the actual selected helper exception. No supplied helper-execution or caller-clock premise. Entry op binding and actual source normal/exception remain explicit; gas-or-terminal progress/helper prices and global reachability remain open.
- Added reproducible untrusted generate-original-dispatch-syntax.py: parses only unchanged op_dispatch, refuses overwrite, exact reproduction cmp passed. Lean body_shape and semantic proofs check its output. Failed attempts involved reserved identifiers, a missing Bool simplifier name, explicit iota normalization and unwanted identifier substitution; only final successful log is indexed.
- Successful dispatch-provenance-v3.log1754jobs, exit0, permitted axioms, MaxRSS1833340KiB. Index4979modules/8458facts; inventory4992modules, unchanged baseline/replacement closure0. Incremental policy61861entries/2255245903bytes, infinity claim, no whole-program K/full verification. Account29% used/0 reset credits.
- Continue capped aggregate rollback pricing and actual opcode gas progress, then child completion and remaining initialization/input/creation/global-count/weighted-target obligations. No milestone stop point.

## Actual JUMPDEST/STOP dispatch and capacity-capped rollback aggregation — 2026-10-18

- pc_add actual body/caller derives mapped pc, original wrapping addition and exact one-word write, preserving physical regular budget/used field. The real normal outcome derives the outer call clock, with no prospective mapping or pc non-wrap premise.
- Complete original JUMPDEST body/caller and literal opcode91 dispatcher selection compose actual charge_gas1 and pc_add1. Real used counter increases1; budget stays equal. Body2source clocks/helper caller3/dispatch caller4, all funding derived. Original STOP0 clears actual running104 and preserves used/budget; body1/helper caller2/dispatch caller3. This covers normal gas-progress and terminal examples, not all opcode exceptions or complete run_frames.
- JournalCappedAggregate proves2*triangle(n)+n=n*n, each n<=C gives2*triangle(n)<=(C-1)*n, and therefore summed original rollback prices <=(38D+40+19(C-1))*totalRestored across arbitrarily many separately capped restores. Existing real CounterLedger bounds totalRestored<=initial+appended; final-family physical potential closes the amortized inequality. Numeric physical slope10210508821 is checked, not a whole-program runtime K. Actual per-call cap/ledger/count/cumulative inequality construction remain open.
- Successful dispatch-basic-normal-v1.log1688jobs, exit0, permitted axioms, MaxRSS1824652KiB, elapsed7.95s. Earlier failures concerned multiplication association, a hand-calculated constant, an omitted Calls import, cases-normalized reflexivity, empty-locals projection rewriting and canonical memory/clock equalities; only successful current-source log indexed.
- Index4985modules/8480facts; inventory4998modules, unchanged baseline/replacement closure0. Incremental policy61867entries/2255281305bytes, infinity claim/no K/full verification. Latest account30% used/0 reset credits.
- Continue actual stack/opcode preservation and gas-or-terminal progress, child completion/log/union, source initialization/input/creation/global counts and weighted target transport. No milestone stop point.

## Actual stack-pop calls and59 original positive-charge prefixes — 2026-10-18

- Actual stack_pop body derives mapped sp, its actual stored word, nonzero underflow check and exact sole sp−1 store. It has zero body source clocks, preserves all other words, the physical regular budget and used counter. No data read, guard outcome, successful store or helper execution is assumed. The original tuple return remains actual.
- Added general return/PureGuard-prefix/scoped-call inversions. The real tuple declaration derives positive caller clock, true callee/return-shape checks and actual normal continuation, including lexical restoration. StackPop.call_normal makes the continuation entry canonical with just sp store, one clock and actual returned binding; arbitrary chains compose with exact source-clock count and no gas/nonlocal mutation.
- OpcodeChargePrefix composes those actual pops with the real literal charge and reaches the actual source suffix; regular budget is retained and actual used counter increases by the charge. Generated59 original helper cases are checked against their unchanged Guest bodies, including all0/1/2/3pop prefixes and literal charge values. Positive progress is proved at actual suffix entry; suffix preservation, exception exits, global reachability/event counts and target work remain open. No full opcode/global bound is claimed.
- Reproducible untrusted generate-opcode-charge-sites.py only recognizes literal leading pops/charge, refuses overwrite; exact reproduction cmp passed. Body_shape uses explicit AST unfolding after raw rfl failed; failed logs never indexed. Other local failures were original ShapeHOL/PanOp constructor spelling, nested raise-shape case splitting, evaluator match/iota reduction and a projection expected-type unification; fixed explicitly. A cross-filesystem rename failed before generation, corrected by copy/unlink.
- Successful opcode-charge-sites-v3.log1694jobs, exit0, allowed axioms, MaxRSS2005612KiB, elapsed11.58s. Index4993modules/8491facts; inventory5006modules, unchanged baseline/replacement closure0. Incremental policy61875entries/2255317778bytes, infinity claim/no whole-program K/full verification. Latest account30% used/0 reset credits.
- Continue original stack/suffix footprint preservation and actual gas-or-terminal progress, child completion/log/union, source initialization/input/creation/global-count reachability and weighted target transport. No milestone stop point.

## All-outcome arithmetic effects and actual free-slot stack_push — 2026-10-18

- LocalEffects erases only locals/clock; its equality retains memory/globals/code/FFI/domain and every other field. Checked primitive/assignment/declaration/branch/sequence/return/raise/break/continue, actual while including timeout, and actual tail/ignored/local-result/scoped calls including failed lookup/shape/destination and exceptions. Installed callee-code conditions are explicit; no callee success trace is assumed. No loop count or helper runtime price follows from this frame theorem.
-44 original arithmetic helpers now compose those rules against the real Guest AST. A checked finite code catalogue and actual-call wrapper retain every nonlocal field/physical gas budget/used counter at every clock and outcome. The catalogue includes exp, shifts, multiplication, comparisons and byte conversions; excludes actual workspace-writing division/modular paths. Its code-map reachability remains explicit.
- Reproducible untrusted generate-arithmetic-effects.py computes candidate closure from unchanged pp source, parses original AST constructors and emits explicit proof steps; exact reproduction cmp passed. Earlier generic proof search timed out on large helpers even with higher heartbeats. Replaced it with direct AST-directed proofs at default budgets. Earlier failures also covered missing carrier import, if/match normalization, redundant tactics, reserved scoped identifier, an unsupported goal-match syntax, generated bullet indentation and an empty context type annotation. Only final successful current-source log indexed.
- Actual charge_gas normal call now exposes precisely the original liquid/used-word writes; every other word survives. Actual empty stack_pop body raises EvmErr2 before any mutation/charge at every clock, with explicit original exception shape.
- Full original stack_push on sp<capacity<=1024 derives actual sp/cap mappings, skips both genuine guards, executes the actual four-word value store and sp+1 store/return/scopes. Every reached store mapping is derived. Under explicit stack destination/gas-cell separation, regular budget/used word survive; sp increment is natural, nonwrapping. All outside-word framing is retained. Body spends0source clocks because no call/loop is taken, NOT0target work. Growth path and actual push caller/opcode composition remain open.
- Successful arithmetic-stack-effects-v1.log1687jobs, exit0, allowed axioms, MaxRSS1820556KiB, elapsed4.66s (final incremental closure replays checked44-helper results). Index5006modules/8526facts; inventory5019modules, unchanged baseline/replacement closure0. Incremental policy61888entries/2255443385bytes, infinity claim/no whole-program K/full verification. Latest account31% used/0 reset credits.
- Continue actual stack depth/free-slot derivation, push caller and complete arithmetic opcode progress; then other opcode/exception/child paths, all remaining initialization/input/creation/global counts and weighted target transport. No milestone stop point.

## Exact stack-depth flow and complete AND/OR/XOR/NOT dispatch — 2026-10-18

- Strengthened actual pop-chain contracts with exact natural depth decrease and every outside-sp word frame; the actual regular charge's two-cell footprint carries depth and all other fields into the real suffix. All59 original charge-prefix cases export these facts. No speculative mapping, successful pop or stack-room premise.
- UnaryCallData derives actual argument arity/value/formal shape/callee binding from successful code lookup. Original stack_push ignored caller now derives its tuple/checks/available1clock and full actual body/caller restoration; under explicit free-slot/header/stack separation, physical budget/used word survive, actual sp increments naturally and stays within capacity. The common push+pc+return suffix derives2source clocks and every full postcondition.
- ScopedCallData/LocalEffectsPrefix/ArithmeticEffectsScoped derive a true scoped arithmetic callee return and real continuation with only caller local binding/clock changed. Argument/code/shape/funding/callee execution are derived from actual normal execution. The helper's price is still separate.
- Complete unchanged AND/OR/XOR/NOT body/caller/dispatcher contracts now compose true pops, charge3, tuple push, pc, zero return and all lexical/caller restoration. Actual pops derive free existing room from incoming physical depth<=capacity<=1024. Final physical regular budget is equal; real irreversible counter grows3 and final depth+popCount=initialDepth+1<=capacity+popCount. Body source prices5/5/5/4, helper callers6/6/6/5, dispatcher callers7/7/7/6. Literal opcode selection22/23/24/25 is checked against original dispatcher.
- Incoming live stack cells/mappings/code, bounded regular ledger and owned stack-vs-gas-cell separation remain explicit. Current gas/depth contracts alone do not establish complete frame-header/other-object preservation or whole-run invariant; add that ownership frame next, rather than silently reusing entry facts. Stack growth, all opcode exception paths, other opcode bodies, global iteration/event counts and target work remain open. Source clocks omit straight-line work, so these are not target-runtime K.
- Successful dispatch-direct-stack-v1.log1695jobs, exit0, allowed axioms, MaxRSS1863644KiB, elapsed4.46s. Failed local attempts concerned natural word-subtraction normalization, unary-list/shape lemma syntax, same-width word conversion and an Entry constructor mistakenly declared theorem instead of def; fixed explicitly. Failed logs never indexed. Updated59-case generator exact reproduction passed.
- Index5015modules/8539facts; inventory5028modules, unchanged reference/replacement closure0. Incremental policy61897entries/2255482421bytes, infinity claim/no K/full verification. Account31% used/0 reset credits.
- Continue full stack/header/other-object preservation, arithmetic opcode suffix composition, all remaining opcode/exception/child paths, initialization/input/creation/global counts, weighted target transport and final cleanup. No milestone stop point.
