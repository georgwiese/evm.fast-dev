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
