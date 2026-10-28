# Finite runtime bound for the current Pancake program

Prove an explicit uniform finite bound on **formal target evaluator steps** for
**the unchanged current implementation**, under the fixed challenge's gas and
covered-outcome assumptions. Keep the bound reasonably tight. **No numerical
ceiling applies.** Do not replace or optimize Pancake to meet a Yukon score
limit. A score-compatible claim or Yukon submission is not required.

Reference main: `f892870c8682517186860842a3ff5f0dea1aa3eb`, after the authorized
rebase. Actual source: `Guest.Software.guestAst` in `Guest/SoftwareAst.lean`.
Read AGENTS.md, docs/CHALLENGE.md, docs/SUBMISSIONS.md and docs/TESTING.md as
needed. **Do not read CLAUDE.md.** Fixed definitions govern stale prose.

## Completion criteria

- Follow `InitE.Certificate` in `InitE/Challenge.lean`: every mathematical input
  byte list with declared gas at most200000000, conditional on actual covered
  source termination. Derive validity, ownership, gas, allocation and helper-entry
  conditions from that execution; do not assume future success or funding.
- Retain actual accepting output matching and covered rejection/trap cases.
- Source call/loop clocks omit straight-line target work. The existing
  input-dependent finite halt witness at infinity is also insufficient. Prove
  the uniform target-step theorem, evaluate its expression exactly, and review
  dominant slack.
- Preserve source, semantics, ROM, fixed proofs and pinned dependencies. Keep
  claim.json at infinity until an actual finite certificate justifies changing
  it. A K above Yukon's score range does not invalidate this task's objective.
- Targeted Lean builds are not isolated comparator/axiom audit/kernel replay.
  Do not claim final verification without a successful run. Existing restrictions
  on running the full verifier on this machine persist.

## Current status — 2026-10-28

**No global finite target K yet.** Claim infinity; no full verification claimed.
Best overall effort estimate: **40%, plausible30–50%**, relative to current main.
Module counts are bookkeeping. The old10^14–10^18 numerical guess was speculation,
not a theorem or target ceiling.

Checked against current Software syntax and declaration entries:

- Actual installed code, main declaration/mem_init, ordinary memory domain,
  and scratch/frame initialization. Main/startup/decoder cuts retain actual
  lexical execution, stopped alternatives, clocks and nonlocal/FFI observations.
  The closed31-helper request-hash graph preserves both arenas and all three
  SSZ workspace globals on all outcomes, reusing8startup helper proofs. The
  actual reached callee has full physical payload/SI/root data and real ABI.
- Whole header precheck: all outcomes cost≤85body/86caller source ticks.
  Whole input_blob: all outcomes cost≤134217728body/134217729caller source ticks.
  Actual copying derives host presence, mapped stores, original bytes and exact
  outside-memory frame. Input length is mathematical length modulo2^64; passing
  guards derive encoded length≤1073741808 without restricting mathematical lists.
- Actual startup/setup/precheck/copy/stateless entry derives heap ordering,
  aligned copied input≥2701134640, persistent ceiling2952790016 and separation
  from the real64-byte SSZ workspace2701132528. The first header/request offsets
  derive16/44, so declared gas identifies original le64(input,474)≤200000000.
- Actual payload allocation, offsets and guards, transaction variable list,
  withdrawal fixed count, remaining11stores and whole normal payload return
  check. The physical payload gas cell at pl+88 is bounded and survives the real
  caller continuation. Real returned allocations derive room at the persistent
  ceiling; an ordinary-domain geometric upper bound is not allocation room.
- Complete current request decoder return: real80-byte allocation, all ten
  physical fields, quotient/remainder facts, input/gas/heap/control retained and
  normal body sourcecost≤348. Its actual scoped caller also checks.
- Outer p/len/o_wit and five witness slice locals are retained. The actual
  witness declarations and length guard derive its contained12-byte minimum;
  three workspace writes and validator derive first12 and range/order within
  eight source ticks. Pure offset loads retain the actual node-list call.
- All three actual witness-list calls, six output stores and literal return si
  check. Physical node/code/header records survive, with item limits1024/65536/
  1024 and headercount≤256. Actual byte-list body/caller returns cost at most
  2*(sliceLength/4)+2/3source ticks at any returning clock. The allocated array end
  bounds the next frontier, so later arrays preserve earlier records. Original
  input, physical payload gas and final return/caller frames survive.
- Current scratch-store/allocation boundary: a real allocation followed by an
  in-range scalar store below ordinary memory errors immediately; scoped cost≤2.
  Complete _node_rlp_fill cannot return under ordered arena/domain facts and
  every body outcome costs≤3source ticks. A below-domain aligned clear≥32bytes
  costs≤1body/2caller ticks; actual scratch allocation/clear≤4, scratch message
  constructor≤4and frame_new≤6including both cursor snapshots. **Actual caller
  arena transport and covered-outcome classification remain necessary.**
- Cleanup removed the replacement implementation and65stale generated modules
  earlier. Current helper imports now use actual Software/minimal code and
  state interfaces. Examples of Solver closure reductions: request syntax359→64,
  DecoderRuntimeCode357→83, request CountsTrace743→109, StructureStore124→34,
  witness PrefixTrace213→113. Existing namespaces are retained where practical.

Latest successful selected closure: `current-container-memory-v1.log`,1274jobs,
permitted printed axioms only. Historical/current proof index:8116modules/
16358facts; Solver inventory8155, replacement closure0, frozen main files
unchanged. Incremental policy passes64924entries/2482901273bytes. These checks
are not a whole candidate build or full verification. Unselected old proofs
remain historical until their current statements/dependencies are checked.

## Remaining work, in order

1. **Use the complete actual payload image to join current hashing.** RootRun
   selects the same decoder post-state at main, with actual SI0/8/16/24/32 and
   mapped hash argument loads. ReturnedImage now retains raw/extra/transaction/
   withdrawal/balance cells and real offset/count arithmetic, including complete
   transaction-record lifetime. Actual room derives encodedLength+16*txCount≤
   251655056, txCount≤12582752 and total transaction bytes≤251655056. Actual root allocation and all three initialized SSZ workspace pointers now
   reach the same hash caller, with mapped/aligned extents and copied-input
   separation. All five arena/workspace globals now survive current hash calls. Invocation
   joins the actual ABI and full physical payload/SI/root data to that same callee.
2. Bound actual request-root hashing on all relevant outcomes, including errors.
   Actual Merkle pair loops now cost≤2ticks/pair; halving dense work≤3*(cur-1),
   full dense/extension/output suffix≤3*(cur-1)+2*(target-depth)+43, on all
   outcomes. Fixed memory calls, length mixing and u64roots also compose.
   Current depth-prefix/maximum entries recheck with minimal Software imports.
   Actual allocation/fill now includes all failed/partial paths without heap-room
   premises. Complete current Merkle body/caller cost≤88*n+4*budget+48/49 for
   actual n,limit≤2^budget, budget<58 and the same non-timeout observation.
   Actual packing body/caller and exact returned ceil(n/32) tuple now check
   without room/mapping/success hypotheses. Its minimal syntax import closure
   shrinks593→27Solver modules. Complete current byte-list/vector bodies and real ABI callers now compose
   packing, current Merkle, release and length mix, including the actual short
   vector branch. Complete current byte-list/vector normal memory and heap frames
   now compose their actual packing allocation, Merkle call, release and list
   length mix. The real three/four-word callers inherit both frames; temporary
   room is derived from their actual pack return, with no old accelerator or
   temporary-room premise. Complete current progressive body/caller now costs≤88*n+3120/3121 for
   actual n≤134217728 and the same non-timeout observation, deriving≤15rounds
   and actual fold count. Progressive list body/caller costs≤88*n+3168/3169; progressive-byte
   body/caller≤packPrice(n)+88*ceil(n/32)+3172/3173 now check, with exact
   packing return and observed errors included. Container body/caller≤89*n+3168/3169 and six fixed-record hashes now
   check without mapped-pointer/workspace/heap-room/success assumptions. Fixed
   record body prices: withdrawal758, deposit1425, wdreq880, cons1144, bdep1279,
   bexit734. Complete actual request-list dispatch/loop/body/caller now checks: body
   ≤(selectedRecordPrice+90)*n+3173, caller adds1, actual n≤134217728 and fixed
   selected record size. No mapping/heap-room/workspace/success premises. Full
   payload/request-root composition and real ownership/resource frames remain
   open. Container syntax/bit-loop/suffix import
   closures shrink613→9/614→40/616→128Solver modules. Shared local-prefix
   soundness now handles byte stores; ByteStoreLocal reuses it.
   Current sha256_pair now has a checked syntax certificate: it preserves all
   globals, spends0body source ticks and at most1caller tick on all outcomes.
   Its1,022-line generated effect proof is now50lines, using shared structural
   soundness. Its checked output-memory frame now preserves every word outside its32output
   bytes on every body outcome, with real normal-caller ABI transport. Scalar-root
   zero/copy/return now preserves words outside its actual32-byte output, with
   real caller transport. Aligned copy/zero and unaligned short-zero memory
   frames recheck with minimal actual Software imports (copy/zero closure246→96,
   short-zero266→119, ZeroCost231→49). Packing now derives its actual returned tuple, persistent request room, next
   aligned/monotone/bounded heap and protected word below the real cursor. No
   allocator-room premise or old134217728-byte packing cap is used. Shared
   actual padding arguments serve both cost and frame proofs. A structural
   call-free-loop certificate proves actual copy/zero preserve every global.
   Actual dense/extension pair loops now preserve protected words using their
   real output slots and current counters, without SHA-input mapping or old
   workspace assumptions. Complete current buffer copy/clear/shrinking dense/
   extension/output/release now preserves protected words outside its actual
   temporary buffer and final32-byte output, on the same normal return. Heap
   mark/release/copy-return frames also recheck with real Software/minimal
   imports (heap scope225→22, copy-return252→114, heap-return227→27Solver
   modules). Shared SavedHeapReturn derives actual final-release assignment
   validity instead of assuming an intermediate heap cell. Its structural
   certificates instantiate current nonempty Merkle, all six fixed records,
   progressive hashing and progressive byte/container/request-list bodies:
   every actual normal return restores the entering heap exactly, without
   numeric/capacity/workspace/mapping/room premises. Complete actual Merkle
   body and caller now retain the protected metadata word and entering heap,
   including actual log/max depths, the empty zero-table copy, normal allocation
   room and full buffer suffix. Context contains the real code/domain, zero
   table and incoming persistent cursor; source n/limit and physical arenas
   remain explicit call-entry facts. Full-byte-list/progressive/fixed-record/
   payload/request-root memory composition remains open. Complete actual container
   body/caller memory and heap frames now check, including the real64-byte
   allocation, progressive call, activity clear/bit loop, output SHA and release.
   The memory proof requires n≤256 for its32-byte activity mask; actual callers
   use19 and5 fields, to be joined at those parents. Its broad failure cost
   theorem remains unchanged. Complete actual progressive
   list/byte wrapper memory and heap frames now check, with real ABI callers,
   packed tuple/count and arbitrary length word. Shared last-output ABI/caller
   reasoning serves software SHA and length mixing, retaining all previous
   theorem interfaces and removing duplicate inversion. Complete actual progressive
   body/caller memory and heap frames now check: real768/32-byte allocations,
   capped geometric rounds, actual terminal round, accumulator clear/fold and
   final output/release. Shared normal allocation inversion derives real room
   and next context for the same continuation. The fold memory proof needs only
   its actual accumulator output, with no SHA-input mapping/digest premise.
   All six actual fixed-record
   bodies/callers now preserve metadata and restore their entering heap. Their
   field extents come from the physical record/chunk arenas; the same allocation
   derives temporary chunk room. Field pipeline local preservation is shared
   by cost and memory proofs. Both actual byte-vector
   branches and byte-list now restore the entering heap on normal return, including
   the list length mix after release. Actual st_le32/st_le64 and length mixing
   preserve words outside their real output/length chunk. Shared byte-store
   syntax checking now handles a bare pointer directly. Large
   straight-line target work remains open; old accelerator Workspace/entry/cost
   proofs are not current. Older hash layouts
   also pin a134217728-byte budget, so check/relax those limits using current
   physical resource facts. Reuse other hash/serialization proofs only after
   checking syntax, indices, imports and all entry premises. Materialize remaining
   witness SI fields at the caller that needs them. Treat chain/output values
   generically when their numeric contents do not affect runtime.
3. Prioritize actual early scratch access and its covered-outcome consequences
   before expanding map/crypto/EVM migration. Main's scratch pointers are below
   sourceBase2701131776 and outside ordinary memory. NoReturn alone does not
   exclude covered terminal FFI paths. Prove caller arena transport and price
   all remaining reachable paths before pruning obligations.
4. Bound reachable current Patricia maps, software crypto, validation,
   execution/gas/refund/child calls, journal/rollback, serialization/output and
   failure/unwind work. Derive global event/resource totals and helper entries.
   Replace obsolete hash-table/accelerator assumptions with actual current code.
5. Check current compiler static facts; compose weighted source work/clocks
   through actual compilation, bootstrap/oracles and target evaluator. Evaluate
   a literal finite K; remove dominant unjustified slack.
6. Final cleanup of obsolete scaffolding/proof branches, retained dependency/
   evidence checks and applicable validation. Do not substitute a conditional
   interface for an unclosed global obligation.

## Working rules and recovery

- Continue autonomously, without milestone approval stops. **Push georg after
  every commit**, using the existing credential helper without printing tokens.
  Do not run Yukon submission or merge a PR.
- Check account usage regularly with /tmp/init-e-account-usage.py. The requested
  reset means an account usage-limit reset. Latest:28%weekly,0resetcredits,
  ordinary usage allowed. Do not claim to control a reset without a tool.
- One selected build at a time, two Lean slots, cache disabled, **8GiB whole-host
  used-memory stop guard**. Stop disk>85%. Poll live builds; do not restart them
  or edit active dependencies. No unqualified full build, Solution build or full
  verifier merely to check a helper.
- Permitted axioms: propext, Classical.choice, Quot.sound only. No proof holes,
  native axioms or fixed-source/dependency changes. Only Solver, Solution and
  claim survive Yukon overlays.
- Index only terminal successful logs matching unchanged source. Run
  record-proof-build.py, original-plan-inventory.py, check-solver-policy.py and
  git diff --check for coherent checkpoints. Incremental policy is not full
  verification.
- Preserve the five untracked pre-rebase RLP files until their current checks
  pass; they are not current proof successes.
- Old head20080445b4247372ec639a2133558441111cdf54 is preserved locally/on georg
  as codex/pre-upstream-rebase-20261027; restored RLP stash
  0d43ada2a12374ec0432fd3f46edfef512bdce99 is retained.

Records: [PROGRESS](work/agent-notes/PROGRESS.md),
[proof index](work/agent-notes/proof-checks.json),
[inventory](work/agent-notes/original-plan-inventory.json),
[rebase notes](work/agent-notes/UPSTREAM-REBASE-20261027.md).

The previous381-line plan is preserved byte-for-byte in
[pre-witness summary](work/agent-notes/BOUND-PRE-WITNESS-SUMMARY-20261027.md),
with its hash in [manifest](work/agent-notes/witness-plan-cleanup-20261027.json).
Earlier large task/progress histories remain archived as described there.
Historical program indices, numerical gates and conflicting instructions are
superseded by the user's current goal and this plan.
