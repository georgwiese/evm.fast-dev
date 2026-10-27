# Finite runtime bound for the current Pancake program

Prove an explicit uniform finite bound on **formal target evaluator steps** for
the unchanged current implementation, under the fixed challenge's gas and
covered-outcome assumptions. Keep the bound reasonably tight, but **no numerical
ceiling applies**. Do not replace or optimize Pancake to meet a Yukon score
limit. A score-compatible claim or Yukon submission is not a completion requirement.

Active reference: official main `f892870c8682517186860842a3ff5f0dea1aa3eb`, after
the user-authorized rebase. Actual source: `Guest.Software.guestAst` in
`Guest/SoftwareAst.lean`. This plan supersedes the archived historical plans.

## Scope and completion criteria

- Follow `InitE.Certificate` in `InitE/Challenge.lean`: every mathematical input
  byte list with declared gas at most 200,000,000, conditional on actual covered
  source termination. Derive extra validity, ownership, gas, allocation and
  helper-entry conditions from actual execution; do not assume future success.
- Preserve source, semantics, ROM and fixed proofs. Retain accepting output
  matching and covered rejection/trap cases from the actual observation relation.
- A source call/loop clock bound omits straight-line work. An input-dependent
  finite halt witness already exists at infinity. Neither is the requested
  uniform target-step bound. Evaluate the final proved expression exactly and
  review dominant slack; produce the quantitative theorem and checked evidence.
- Keep `claim.json` at infinity until an actual finite certificate justifies
  changing it; do not alter it merely to fit a score format.
- Targeted Lean checks are not isolated comparator/axiom audit/kernel replay.
  Do not claim final verification without a successful run. Existing restrictions
  on running the full verifier on this machine persist.

Read `AGENTS.md`, `docs/CHALLENGE.md`, `docs/SUBMISSIONS.md`, `docs/TESTING.md`
and actual contract/semantics as needed. **Do not read `CLAUDE.md`.** Some prose
arena descriptions are stale; use the fixed definitions.

## Current status — 2026-10-27

**No global finite target K yet**; claim remains infinity, no complete verifier
run claimed. Best overall effort estimate: **40%, range 30–50%**, relative to
current main. Module counts are bookkeeping, not completion percentages. The
earlier speculative K guess, 10^14–10^18, is not proved or a target ceiling.

Checked against the current Software AST:

- Actual installed-code/declaration-pass/evaluation-preservation interfaces;
  generic helpers shed old host/map/hash dependencies.
- Actual continuing shared reads derive presence, replies and scalar values.
  Reached gas word is at most 200,000,000 under canonical offset facts; deriving
  those facts at the genuine caller remains open.
- Whole header precheck: every outcome costs at most **85 body /86 caller source
  ticks**. Its actual signed small-count offset loops include failed accesses
  and decoder exceptions.
- Whole `input_blob`: every outcome costs at most **134,217,728 body /134,217,729
  caller source ticks**. The stride-eight loop costs `(length + 7 - i)/8`;
  length comes from the actual load and passing guard. Allocation/trap failures
  are included without future readability, room or store-success premises.
- Actual normal copy-loop execution now yields its exact state, observed host
  presence/destination mappings, input-byte correspondence and an exact frame
  outside copied words. This composes through the real i/w scopes and tuple
  return. Actual continuing length reads identify input.length modulo 2^64,
  deriving header presence even for word-overflowing mathematical list sizes.
  BlobReached now joins the actual allocator, complete body and returning caller:
  it derives real room, the encoded-length bound, tuple binding, byte image,
  exact heap update, paid clocks and protected-word frame. Initial heap cursor,
  alignment/endian/oracle invariants still need derivation from actual main.
- Allocator/trap/input catalogues use actual Software function entries 2/0/24.
  Shared local-summary composition and fixed counter increments are generic.
- The actual memzero body/ignored call cannot continue from an aligned clear of
  at least32bytes below sourceBase. The genuine scratch allocation derives its
  room/rounded pointer/alignment before this clear. Current msg_new_scratch and
  frame_new (including both real cursor snapshots) cannot return under ordered
  bounded arena cursors and the actual domain. These are conditional control
  facts, not yet whole-path exclusion or covered-outcome classification.
- Current main entry and its genuine mem_init prefix now build: main function
  index812, 67 scalar declaration globals, heap=@base, scratch=2701127680 and
  frame_mem=2688618496. Entry.base comes from the actual source declaration
  frame. Every actual terminating source behavior reaches this computed prefix.
- CurrentStartup now checks the actual closed startup/decoder/result-writer call
  graph (46 helpers), preserving both arena globals on every outcome. Prefix
  reconstructs the literal13initializer calls after mem_init and proves their
  exact evaluation cut: each actual termination either stops inside that prefix
  or reaches the real following main state with both initialized cursors retained.
  This is not an initializer runtime bound or a proof that every input reaches
  the suffix. DecoderPrefix now reconstructs the real six lexical actions through
  the caught decoder call and joins their actual continuation/early-stop cut to
  whole source observations. It retains live out/z32/si/err_code bindings and
  preserves the full nonlocal observation on stopped paths. DecoderReturn proves
  the real rejection handler cannot fall through and extracts the actual checked
  scalar decoder return from a completed prefix. Normal startup host/heap facts
  and the internal decoder input/lifetime joins remain open.
- CallPrefix drops the unrelated ClockCostScopeLocals umbrella; its transitive
  Solver closure falls from155to7modules. The trace closure falls158to10.
  Existing clock-only interfaces are retained as projections of the stronger
  stopped-state classification. CaughtAssignedStops and NoFallthrough also use
  their actual minimal imports. These are proof dependency changes, not changes
  to the fixed guest or semantics.
- Replacement implementation/closed proofs/generators/harness were removed
  earlier. Another 65 closed stale generated modules were removed after rebase.
  Other old-program proofs remain historical until their current dependencies
  and statements pass real checks.

Latest successful closure: `current-decoder-return-v5.log`, 354 jobs,
permitted printed axioms only, 3.88 seconds, MaxRSS 1,476,300 KiB.
Historical/current index: 7,861 modules /15,426 facts; 245 modules carry the
current dependency reference. Incremental Solver/package policy passes at
64,664 entries /2,480,839,957 bytes.
These checks are not full verification.

## Remaining plan

- [x] Rebase onto latest official main; preserve old checkpoint and stashes.
- [x] Remove replacement implementation/unused closure and closed stale generated
  modules; retain shared helpers needed by actual current-program proofs.
- [x] Retarget core code installation, actual shared reads, current header cost
  and complete input-copy cost; clean their stale dependencies.
- [ ] Derive the checked input body/caller's initial heap/oracle/alignment facts
  from actual main and carry the image through its decoder lifetime. Port remaining HostLength/HostWords/
  HostGas callers; old unconditional backing claims are stale. Close actual
  offset guard semantics/decoder reachability/gas.
- [ ] Derive current main initialization, allocation geometry, memory ownership
  and input/heap/scratch lifetimes. Input maximum is 1,073,741,808 bytes; allocation
  ceiling is 2,952,790,016. Scratch is below sourceBase and outside compiler ordinary
  memory; analyze actual covered execution rather than assuming it excludes all
  valid inputs. Retain arbitrary mathematical list sizes, including word wrap.
  Prioritize checking the earliest actual scratch access and its covered-outcome
  consequences before expanding the map/crypto migration. CurrentDomain now
  proves every ordinary address is at least sourceBase and that scalar stores
  below it fail immediately; no whole-path unreachability is claimed yet.
  The initial arena cursors now follow from the real main/mem_init prefix.
  Their transport through the13startup calls now has an exact whole-main cut.
  The actual six-action decoder cut now retains its lexical scopes and both
  arena globals; successful continuation derives the actual scalar decoder return.
  Next derive normal startup host/heap facts, join the decoder's actual input_blob
  and decode_stateless_input calls to its copied image/lifetime, and classify
  scratch helper outcomes. NoReturn alone does not rule out covered terminal
  FFI outcomes, so do not discard later EVM/map obligations on that basis.
  AllocationArithmetic/AllocationNormal/AllocationCall/AllocationCallNormal now
  use the actual 2,952,790,016 ceiling. Extended Expected/Global/Local variants
  and their old callers still require migration.
- [ ] Bound actual Patricia maps and software cryptography. Reuse unchanged
  proofs only after checking current code, indices and dependencies; obsolete
  table/accelerator contracts do not discharge the new obligations.
- [ ] Complete serialization/traversal/hash/root and persistent graph ownership,
  EVM/gas/charge/refund/child calls, journal/rollback, output and covered failure/
  unwind paths. Derive global event/resource totals and genuine helper entries.
- [ ] Regenerate/check current compiler static facts. Compose weighted source
  work/clocks through the actual compilation, bootstrap/oracles and target
  evaluator. Evaluate a literal finite K and remove dominant unjustified slack.
- [ ] Final cleanup of remaining obsolete scaffolding/proof branches; refresh
  retained dependency/evidence checks and applicable final validation. Do not
  substitute a conditional interface for a closed global obligation.

## Working rules and recovery

- Continue autonomously; no milestone approval stops. **Push to georg after
  every commit**, using the existing credential helper without printing tokens.
  Do not run Yukon submission or merge a PR.
- Check account usage regularly with `/tmp/init-e-account-usage.py`. User means
  account usage-limit resets. Last check: 7% weekly used, zero reset credits,
  ordinary usage allowed.
- One selected build at a time, two Lean slots, artifact cache disabled,
  **8 GiB whole-host used-memory stop guard**. Stop if disk exceeds 85%. Poll
  existing live builds rather than restarting. No unqualified whole build,
  baseline audit or Solution build merely to check a helper.
- Permitted axioms: propext, Classical.choice, Quot.sound only. No proof holes,
  native axioms, fixed-source changes or dependency updates. Only Solver,
  Solution and claim survive Yukon overlays. Preserve pinned dependencies.
- Index terminal successful logs only, matching unchanged checked source.
  Use record-proof-build.py, original-plan-inventory.py, incremental
  check-solver-policy.py and git diff --check for coherent checkpoints.
- Five unfinished pre-rebase RLP files remain untracked; preserve until current
  dependency checks pass. They are not current proof successes.
- Old head 20080445b4247372ec639a2133558441111cdf54 is preserved locally and on
  georg as codex/pre-upstream-rebase-20261027. Restored RLP stash
  0d43ada2a12374ec0432fd3f46edfef512bdce99 is retained.

Current records: [PROGRESS](work/agent-notes/PROGRESS.md),
[proof index](work/agent-notes/proof-checks.json),
[inventory](work/agent-notes/original-plan-inventory.json),
[rebase notes](work/agent-notes/UPSTREAM-REBASE-20261027.md).

The previous 930 KB task document and 1.17 MB progress document are preserved
byte-for-byte as [task history](work/agent-notes/BOUND-HISTORY-PRE-CLEANUP-20261027.md)
and [progress history](work/agent-notes/PROGRESS-HISTORY-PRE-CLEANUP-20261027.md),
with hashes in [archive manifest](work/agent-notes/rebase-cleanup-history.json).
Their old program indices, numerical gates, plans and conflicting operational
instructions are historical; later user instructions and this plan govern.
