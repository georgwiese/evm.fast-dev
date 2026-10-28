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

Latest successful selected closure: `current-parent-requests-cost-v2.log`,1396jobs,
permitted printed axioms only. Historical/current proof index:8131modules/
16410facts; Solver inventory8170, replacement closure0, frozen main files
unchanged. Incremental policy passes64939entries/2482976892bytes. These checks
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
   The same callee now also receives the complete actual request image: all ten
   physical pointer/count fields, exact start/size, validated offsets, quotient/
   remainder counts, real input/RQ arenas and allocation ordering. Its persistent
   room derives encodedLength≤251655056. Each request list derives its actual
   physical byte extent and count≤134217728; all five share one exact encoded
   byte budget and total count≤(requestSize-20)/68.
2. **Finish the actual payload/request-root hash joins.** Current helper source
   costs are checked on all relevant outcomes (same actual non-timeout execution
   where required), without future success, mapped-input or allocator-room
   premises. Complete Merkle body/caller≤88*n+4*budget+48/49 for n,limit≤2^budget,
   budget<58. Packing derives its exact returned(buffer,ceil(n/32)) tuple and
   costs packPrice(n), n+64<2^64. Byte list/vector bodies/callers compose packing,
   Merkle, release and mix, including the actual short vector branch. Progressive
   body/caller≤88*n+3120/3121 for n≤134217728, deriving≤15actual rounds and real
   fold count. Progressive list≤88*n+3168/3169; progressive bytes≤packPrice(n)+
   88*ceil(n/32)+3172/3173; container≤89*n+3168/3169. Fixed-record body prices:
   withdrawal758, deposit1425, wdreq880, cons1144, bdep1279, bexit734; caller+1.
   Actual selected request-list body≤(recordPrice+90)*n+3173; caller+1.

   Normal memory and heap frames now check for complete Merkle, packing, byte
   list/vector, progressive hash/list/bytes, all six fixed records, container
   and selected request-list, with real ABI callers and lexical restoration.
   Actual returned allocations derive persistent room, mapped temporary arenas
   and next aligned/bounded heap; ordinary-domain extent is never substituted
   for allocation room. Physical input/output/workspace/current-heap/count facts
   remain explicit call-entry obligations. Container memory needs n≤256 for its
   32-byte activity mask; actual parents use19 and5, still to be joined there.
   Request-list frames include all five literal tests, the selected record hash,
   real input/output slots, counter advance, root-array allocation and final
   progressive list/release. Earlier metadata survives outside the actual output,
   length chunk and temporary buffers; normal whole-helper returns restore heap.
   Software SHA's checked body writes only32output bytes, preserves all globals,
   costs0body/1caller source tick, and needs no SHA-input mapping/digest premise
   for its memory frame. Its straight-line **target** work remains open.

   Cleanup shares source argument/ABI/output-call, saved-mark, allocation-context,
   field pipeline and actual copy/zero effect proofs. Minimal current Software
   imports replace obsolete accelerator closures; the replacement implementation
   and65stale generated modules were removed earlier. Historical unselected
   proofs remain unclaimed. These are normal memory frames plus separate
   all-outcome costs, not a proof that hashing succeeds or that errors are covered.

   Still open: derive every actual parent count/read/byte total from the same
   complete payload and request decoder images, and transport them across the
   parent hashes. Join actual root/payload/request allocations and outputs to
   those frames and compose whole current payload/request-root costs, including
   earlier stopped alternatives. Recheck old layout limits against actual
   encodedLength+16*txCount≤251655056, txCount≤12582752 and totalTxBytes≤251655056.
   Full request fields now reach the actual root callee; their list extents,
   individual count bounds and shared byte/count budgets check. Actual parent
   request syntax, normal heap restoration and all five list ABIs now check.
   Their checked list-price sum≤13*(requestSize-20)+15870 uses the shared
   input budget. Complete actual htr_requests now has body/caller source cost
   ≤13*(requestSize-20)+19488/19489, including failed allocations and all
   observed non-timeout outcomes. Every real continuing list call derives the
   next complete RQ image and restored heap before later reads. Its actual
   allocation return derives the fresh160-byte chunk extent, persistent room
   and next bounded/aligned frontier. Remaining caller/root entry obligations
   are the real decoder image, installed code/domain, workspaces and frontier;
   no future helper success or extra temporary room is assumed. Materialize
   further SI witness fields at the real caller that needs them. Treat digest/output values generically when their values do not
   affect runtime. Review dominant copy/zero and empty-progressive slack later.
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
