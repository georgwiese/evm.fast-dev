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

Latest checked step: exact validated list items/count, real slice records,
actual allocation/heap update and memory frame; current decode_header's normal
list prefix reaches those records at≤103*length+17 source ticks. Shared scalar
assignment imports reduced124→8 Solver modules. Main connection replay1966jobs
and header-prefix884jobs passed. Whole header/stopped-path composition remains
open, followed by later current source paths and target-step composition.

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

Latest successful selected closure: `current-arena-interface-main-list-cleanup-v1.log`,1910jobs,
permitted printed axioms only. Historical/current proof index:8241modules/
16688facts; Solver inventory8281, replacement closure0, frozen main files
unchanged. Incremental policy passes65051entries/2483475170bytes. These checks
are not a whole candidate build or full verification. Unselected old proofs
remain historical until their current statements/dependencies are checked.

## Checked source stages and remaining work, in order

1. **Checked: actual decoder image and hash-entry derivation.** RootRun
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
2. **Checked source hash bodies/callers; target cost remains open.** Current helper source
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

   The complete current payload body and real two-word caller now have source
   allowance5*totalTxBytes+3391*txCount+848*withdrawalCount+5*balanceBytes+
   16695/16696. This includes the actual initial raw load, outer mark/608-byte
   chunk allocation, static fields, extra-data list, transaction declarations/
   mark/root allocation/loop/list/release, assigned withdrawal root allocation,
   withdrawal loop/list/release, balance hash, nineteen-field container and
   final release. Each real normal prefix derives the next complete physical
   payload and heap before later field reads. Failed allocations and all
   observed non-timeout outcomes remain included. Validated offsets derive
   real raw/withdrawal/balance arenas and counts, without a sixteen-withdrawal
   premise or any future successful hash/extra temporary room. Whole payload
   body and actual caller now protect arbitrary earlier metadata outside their
   actual output/length chunk and restore entering heap on the same normal
   return, through all real allocations and scopes. Literal raw+0
   expressions are retained, and their compiled target work remains unpriced.

   Full request fields reach the actual root callee. Its five list extents,
   counts and shared byte budget, actual160-byte chunk allocation, complete
   source body/caller cost13*(requestSize-20)+19488/19489, and whole protected
   memory/heap caller frame check. Actual normal prefixes supply each next RQ
   image; failed allocations and observed non-timeout outcomes are included.

   The complete actual root body/caller now compose the four child calls,
   real saved mark/128-byte chunk allocation, Merkle and release. Both child
   entry contracts derive from the same decoder state and actual root
   allocation; normal prefixes preserve all complete SI/RQ/payload images.
   Body allowance is the four caller prices plus413; the actual main caller
   adds one. Every observed non-timeout stopped prefix is included. The whole
   normal body and main caller protect earlier memory outside their actual
   output/length chunk and restore entering heap. These are source costs and
   normal frames, not target steps or covered-terminal classification.
   Main's actual normal root return now also carries all three original
   witness record arrays and all six physical SI40/48/56/64/72/80 fields,
   with exact slices, lengths and headercount≤256. The actual pre-root heap
   bounds their extents; one shared image/frame and argument-load proof handles
   all three arrays, including empty arrays. Initialized scratch/frame cursors,
   domain, workspace and persistent frontier also survive that same return.
   Actual main verification entry and all eight wrappers now select the same
   current run_attempt execution with those physical inputs and bounded gas.
   The actual first payload declaration/skip exposes its real header caller
   and argument loads, retaining lexical restoration and stopped alternatives.
   Main's later serializer/output continuation remains explicit and unpriced.
   Wrapper imports drop1601→54 and verify-program1603→56 Solver modules after
   removing the obsolete header/EVM interface and checking current entries.
   Current RLP byte-header body/caller cost≤10/11, real normal return
   derives positive nonwrapping item extent, and one actual validator body
   step costs≤13. A real scratch allocation followed by storing an existing
   caller word cannot continue below ordinary memory. Parser Solver import
   closures drop251→56 (HeaderCost) and243→48 (ReadLengthCall); an unrelated
   serializer/U256 carrier import is removed.
   Complete current internal-validator body/caller now cost≤14*(length+1)
   /14*(length+1)+1 under actual initialized scratch/frame/domain facts and
   nonwrapping input extent. Real continuing parses advance inside a fixed end
   or finish; a nested push cannot continue after its actual first scratch
   store. Setup declarations, failed parses/allocations, stopped paths and
   exhausted clocks are included. The old Rlp.Validation.Arena.lower assumption
   remains unused and false for actual initialization.
   Normal internal and public-validator bodies return zero and preserve all
   nonlocal state, including memory, globals and real arenas. Actual caught
   failure handling cannot turn an internal failure into normal continuation.
   The complete public saved-mark/caught-release wrapper and actual caller
   now cost≤14*(length+1)+4/+5, and the normal ignored caller has the same
   complete nonlocal frame. Shared caught-call inversion is FFI-state-generic.
   The complete current rlp_item_total body costs≤14*inputLength+30 on all
   outcomes; a real normal return also derives its positive actual consumed
   bytes, cost≤14*consumedBytes+30 and complete nonlocal frame. Its actual
   scoped caller supplies that same byte advance, exact resumed caller and
   cost≤14*consumedBytes+31. Flat byte-string continuations cost zero source
   ticks. Shared current syntax is separated from legacy mapped-arena costs.
   Complete current list-count body/caller now cost≤46*length/+1, sharing
   one actual byte budget. Real normal returns derive count≤length and a
   complete nonlocal frame; ignored and scoped callers retain that same
   actual count/state. The actual positive item size justifies both counter
   increments without wrap. Literal syntax and assignment proofs are shared
   with historical clients; their mapped-arena contracts remain unclaimed.
   Cleanup separates the unchanged actual ArenaState contract from startup
   implementation imports. ArenaFrame Solver closure97→10, current list-count
   caller245→175 and public validator caller229→159. Main's actual decoder/
   root/verification/header connection and the list-count closure recheck.
   Next: current item/slice/header bounds and actual later callers. Recheck old
   limits against encodedLength+16*txCount≤251655056 and txCount≤12582752.
   Treat digest/output values generically when they do not affect runtime.
   Review dominant copy/zero and empty-progressive slack before the final K.

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
  reset means an account usage-limit reset. Latest:4%weekly,0resetcredits,
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
