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
