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

## Current status — 2026-10-29

**No global finite target K yet.** Claim infinity; no full verification claimed.
Best overall effort estimate: **50%, plausible40–60%**, relative to current main.
Module counts are bookkeeping. The old10^14–10^18 numerical guess was speculation,
not a theorem or target ceiling.

The current startup/input/header/gas/two-database/state-init path is connected
through both actual payload-header indexed tries. The complete unchanged
withdrawal encoder costs≤201body source ticks; its real loop costs≤203 per
row. The actual payload_header execution through both tries either stops or
reaches execution-request encoding within476207133311source ticks, retaining
all decoded inputs and header fields. Any reached continuation has zero actual
transactions and withdrawals, derived from the real trie executions.

These are all-outcome source-clock allowances, not formal target-step bounds.
Actual SHA state/pad globals now survive startup and this complete main prefix.
The request encoder receives the real five-list image, with nonwrapping sizes
and owned input slices before its incoming heap. Each actual iteration costs
≤(its encoded bytes)/8+10source ticks (uniformly31456889). Normal next-model
preservation and the complete loop/hash continuation, remaining main, uniform
target composition, dominant-slack review and final cleanup remain open.

## Earlier checked milestones, in order

Unchanged decode_header208 costs≤195*inputLength+473
body/+474caller source ticks and derives its real fresh header/earlier-memory
frame. Actual software keccak25692 costs≤44*(bytes/136)+689body/+690caller ticks,
with its real24-round permutation and full workspace/output memory frame.
Whole validate_headers212 now costs≤51528322body/+51528323caller source ticks,
covering both allocations and all decode/hash/link loops. Actual normal/scoped
returns supply the real arrays, advanced physical context and protected input.
Selected2227-job current main/root/table and find-leaf helper replay passed. The
actual first three initializer calls derive Keccak state2701132160 and pad2701132360;
these globals survive startup, decoding and the31-helper root graph. Real decoded
witness images supply the header rows and full caller context. Header returns
retain SI/payload/gas, all witness images and the advanced heap. Later current
source paths and uniform target-step composition remain open.
The real run_attempt now either stops within51528390source ticks or reaches
its first current Patricia database call with full decoded inputs intact. The
current gas-limit check costs≤66body ticks and preserves all nonlocal state;
its complete post-header prefix costs≤67. Actual node records/heap geometry
derive count<2^31, and the unchanged capacity loop selects its sufficient
power of two in≤30ticks. The current Patricia htab_new constructor costs≤8body
ticks at arbitrary entries and≤5body ticks at the real32-byte-key/current-heap
entry. Actual successful returns derive all four request-room facts, the table
value, all11metadata cells and the earlier-input frame. Its real88+72*(capacity+1)
byte layout implies successful power-of-two capacities≤2^21 and corresponding
builder counts≤1048575. These are current constructor contracts; actual
insertion/tree invariants and full builder/source/target composition remain open.
The actual first database child now reaches its real initialized Patricia
table/insertion-loop continuation within36source ticks or stops earlier.
The same caller/callee run derives the constructor workspace, physical header,
array separation, earlier-input frame and resulting count≤1048575; main’s
later codedb continuation remains explicit.
Current htab_find_leaf119 now has a257body/258caller source allowance from a
physical32-byte-key table with an increasing-bit node image. Its actual
step chooses a real child or stops at leaf marker256; invalid key reads and
short-clock outcomes are included. A physical empty table returns0 in0body
ticks without any initialized node/key contents. Deriving/preserving the
increasing-bit image from actual insertions remains open; this helper is not
a global database bound. Normal traversal now returns zero or a genuine
leaf marker256, with full physical memory/global preservation and the actual
scoped caller continuation. A genuine newly returned constructor supplies
the vacuous initial node image and real header/alignment facts.
The unchanged htab_first_diff118 now costs≤9*keyLength body/+1caller,
including failed byte reads, bit-scan early returns and exhausted clocks.
Actual32-byte callers therefore have288body/289caller allowances. A real
continuing bit step skipped a zero digit; falling through its whole8-bit
loop forces the byte xor to zero. The complete actual function now
returns its genuine least most-significant-first mismatch, or256 exactly for
equal keys, with the full physical frame. Its scoped caller retains that same
returned word and original continuation within289source ticks. Actual byte
loads, zero prefixes and every normal/returned loop path are checked. The
insertion history/tree-order connection remains open. Shared counter/local-flow
interfaces now admit actual early returns while preserving existing APIs.

Current htab_new_node122's actual empty-free-list/no-growth path returns the
real next index and writes only its increment, at every body clock including0.
It costs0body/1scoped caller source ticks. The genuine constructor return now
retains its real capacity≥2 and derives this first allocator context. Shared
slot geometry maps all available real keys/nodes/order slots, without assuming
initialized contents. The actual find-leaf key test now observes the real
most-significant-first key bit from physical bytes. Actual normal find-leaf execution now
derives its finite query-directed route to the actual returned leaf, and
the original scoped caller retains that earlier route. A logical routing
model proves common-prefix preservation and excludes insertion stopping at
a bit equal to the real first mismatch. Actual htab_set126 entry/search
syntax is checked. Insertion history still must establish/preserve this
routing model, node availability and full physical keys after updates.
The real insertion second-search step and loop now check:≤257source ticks,
with the actual d/p/key locals and original parent update. Normal exits
retain the real parent edge, route to the earlier lookup leaf and b≥d;
that earlier actual first mismatch strengthens it to b>d. Lookup and
insertion share only a thin physical cursor, with their own real guards.
Its real post-difference header reads/declarations now initialize that same
search and either stop within257ticks or reach the unchanged new-leaf caller
with the actual strict split, parent edge and all three outer restorations.
The search cannot return htab_set on its own; no successful allocation is
assumed to expose this continuation.
A shared physical insertion-only table image now carries the actual header,
geometry, fresh-index range, routing, leaf keys and caller-specific leaf-value
predicate. Its empty base is derived from the genuine constructor; read-only
frames retain it. Current memeq13 costs≤4body/5caller source ticks and its real
normal result identifies byte-key equality at arbitrary alignment. Actual
htab_set's first two mapped loads and scoped lookup now retain the complete
image and reach the original continuation with empty0 or a genuine routed leaf.
Comparison ABI/frame cleanup reduces this comparison's Solver closure93→55.
The real nonempty continuation now reads the actual leaf key and performs
that comparison. Its actual failed-equality path computes the genuine first
mismatch and reaches the unchanged new-leaf call with strict split, parent
edge and retained t/key/value/other caller bindings within546source ticks,
or stops earlier. The actual equal-key branch writes its reached leaf value
and returns0 at any body clock. The complete image now survives that real
write: header, node bits/edges, every leaf key and the value-membership
predicate are preserved using nonaliasing derived from actual array geometry.
Actual aligned32-byte key copying now costs2caller ticks and derives both
its exact four-word memory update and the copied physical key bytes.
Fresh-node insertion remains to prove. Shared image facts
derive fresh indices and two available nodes from the actual processed-count
and sufficient-capacity facts, rather than future successful allocations.
Both original node constructors and scoped callers now check: current
htab_new_leaf123 costs≤3body/4caller source ticks, including the genuine
no-grow allocator,32-byte copy and six node/order/count stores;
htab_new_internal124 costs≤1body/2caller ticks for its allocator and four
real stores. Normal runs derive their own paid clocks and exact memory
update; all stopped outcomes are included. The actual image supplies their
physical header/array facts. Query alignment and its position before the
table remain ownership obligations for the database caller. Fresh insertion
must still preserve the full image after original edge/root rewiring.
The actual empty-table insertion now either stops within4source ticks or
returns0 with the full genuine nonempty table image, after the real leaf
constructor and original root store. Fresh leaf writes preserve all earlier
input, nodes and other physical key slots; its actual parent/value/position/
marker/order cells and updated count/next metadata check. Internal-node
writes likewise retain prior nodes, keys and unrelated header fields.
The pure two-node splice preserves routing/increasing bits; its freshness,
least-mismatch/common-prefix and extended valid-index range are derived from
the actual image and earlier lookup/search route. Connecting the nonempty
original rewiring stores to that image remains open. Thin state-projection
and frame-transport helpers avoid expanding entire nested store states;
the complete first-image check now takes about2.5seconds instead of timing out.
The complete unchanged current32-byte-key htab_set126 now costs≤815body/
816ordinary-caller source ticks, from its actual physical insertion image,
two available indices and earlier aligned query buffer. This includes actual
lookup, comparison, first mismatch, second search, both constructors and all
parent/child/root rewiring outcomes. The real leaf return derives the second
allocator entry; the original rewiring block has0source ticks on every outcome.
The failed-comparison tail costs≤552, nonempty post-lookup≤557; empty
post-lookup≤4. A failed empty insertion cannot fall through to comparison.
This is a complete per-insertion helper bound, not yet a whole-builder/global
bound: nonempty fresh insertion must still preserve the physical image for
the next builder iteration, and actual query-buffer ownership remains open.
The unchanged whole post-constructor splice now has an actual execution
theorem: refresh nodes, all three parent writes, real query-bit child stores,
real left-cell/root attachment and return0. Both constructors preserve the
earlier input/query bytes; every field except memory/locals/clock survives.
The query bit therefore comes from the same physical buffer as the earlier
lookup/difference. Shared metadata/frame helpers replace nine redundant
domain/code projections, while retaining the existing insertion-cost APIs.
Full nonempty image assembly and its real caller composition remain open.
The complete nonempty physical image now checks for the exact combined
constructor/splice memory model. It retains all11header fields, correct
root/count/next updates, extended valid-index range, mapped markers and child
cells, increasing routing, real old/new key bytes and witness-value membership.
Actual parent selection is proved from the original left-cell comparison and
earlier parent link, including the right-edge alternative. Count room is an
explicit current-counter obligation. Real scoped constructor/splice execution
must still transport this image into the same caller post-state before the
builder induction can use it; this is not yet a whole-builder bound.
The full original htab_set body and real ignored-result caller now supply
that builder invariant on every actual normal return. Empty, equal-key and
fresh-key paths all return0, retain a complete physical image with at most
one additional leaf, preserve all nonmemory physical fields and protect every
earlier input word. Caller locals are restored. The failed-comparison proof
uses the same actual mismatch/search/constructor/splice execution, not an
independent successful insertion. The matching815body/816caller all-outcome
cost still checks. Actual builder iteration, query-workspace ownership from
main and later source/target composition remain open.

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

Latest successful selected closure: `current-patricia-entire-insertion-real-caller-v2.log`,981jobs,
permitted printed axioms only. Historical/current proof index:8550modules/
17296facts; inventory8594modules, replacement AST reverseclosure0, fixed files
unchanged. Incremental policy65380entries/2484769018bytes PASS. This is helper
build evidence, not complete verification.

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
  reset means an account usage-limit reset. Latest:48%weekly,0resetcredits,
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

## Actual MPT workspace and shared frame cleanup

Actual current mpt_init223 normal body/caller returns now derive all five
allocations,184bytes of persistent room and the exact global template.
Main's actual first four calls establish mpt_hash_scratch2701134768 and heap
at least2701134824. All nine remaining initializers preserve that pointer
and lower frontier, including the actual EVM mark release. Main's decoder
and root-allocation traces retain the same MPT pointer. No successful future
hash/allocation or source funding is assumed. The previous2701134640 input
lower frontier is too weak to protect against this buffer; propagate the
new derived frontier through physical input/witness images next.

Cleanup moves42large actual-syntax helper proofs into one shared six-key
core; the43existing five-key public interfaces remain thin wrappers, with
mpt_init restricted because it writes the sixth key. Decoder/root prefix
frames now support all six keys. The generator reproduces this layout and
its check-only mode passes. Existing startup/decoder/root API replay passed
1609jobs; actual MPT/main proof replay passed1600jobs. Only permitted printed
axioms. Index8554modules/17343facts; inventory8599modules, replacement closure0,
fixed files unchanged. No global finite target K or full verification.

## Actual input/MPT frontier through the reached database caller

The copied input, decoded SI/payload/request/witness images and all actual
main/root/header continuations now retain the stronger derived lower
frontier2701134824. The real MPT hash pointer2701134768 survives the complete
31-helper root graph, verification wrappers, header validation and gas-limit
prefix to the first actual database child. This follows the current startup
proof; the first-three SSZ-only frontier remains unchanged in its older API.

New shared frames preserve a complete Patricia image through writes below
its actual table and name the actual32bytes of any mapped query buffer.
Thus the real witness hash cannot corrupt the later table or decoded input.
General witness-to-physical-row extraction now serves headers/nodes/codes;
the old header-only interface is a thin wrapper. Original database loop
syntax/live-state and both real hash/insertion argument reads check, with
real hash cost44*(rowLength/136)+690. Whole insertion-loop cost/normal return,
main completion and uniform target-step composition remain open.

Validation: current-mpt-input-frontier-v4.log PASS2201jobs;
current-builder-row-reads-v1.log PASS932jobs. Permitted printed axioms only.
Index8561modules/17354facts; inventory8606/replacement closure0/fixed files
unchanged. Incremental policy65393entries/2484826770bytes PASS. Generator
check-only replay passes and now tracks all eight root-frame keys. No global
finite target K/full verification. Usage21%weekly/0resetcredits. Next: actual
hash/set/counter iteration and complete current node/code database builders.

## Complete actual database insertion loop and aggregate-byte allowance

The original current nodedb_build227 insertion loop now has a checked
all-outcome bound that sums actual row lengths. Every real continuing row
hashes its decoded witness, preserves the complete physical Patricia image,
performs unchanged htab_set and increments its actual counter. It costs
44*floor(rowLength/136)+1506body ticks; with its real loop tick the allowance
is44*floor(rowLength/136)+1507. Actual normal iterations derive the next
image with count≤processed and leaf values restricted to genuine decoded
record addresses. Stopped/failed/short-clock outcomes are covered.

The actual table-constructor return initializes this invariant without
interpreting any uninitialized slot as a live node. The original entire
post-constructor tableTail is priced by the sum; normal loop exits retain
all decoded rows, input, heap/globals and table image. A checked floor-sum
reduction gives≤44*floor(totalPayloadBytes/136)+1507*recordCount, rather than
multiplying each item's maximum size by a separate maximum count. The real
decoded-record byte-budget theorem supplies that aggregate byte allowance.
Full capacity/constructor/body/caller composition and normal builder return
remain next, followed by later current source paths and uniform target K.

Validation: current-builder-loop-initialized-v2.log PASS1518jobs, including
the whole weighted loop, aggregate-byte bound and actual constructor-loop
state. Only permitted printed axioms. Index8569modules/17369facts; inventory
8614/replacement closure0/fixed files unchanged. No global finite target K
or full verification. Usage22%weekly/0resetcredits.

## Complete current database body, literal main bound and normal result

The whole unchanged nodedb_build227 body now costs at most
44*floor(payloadBytes/136)+1507*recordCount+36source ticks. The actual
capacity/constructor prefix supplies live caller locals and its table's
lower boundary. Real decoded node/code images now derive every hash/table
entry condition at the actual callee, including MPT scratch ownership.

An allocation-derived cap refines the count term to min(recordCount,1048575):
inputs above that cap stop within36prefix ticks. Actual nonempty record-array
geometry and the persistent frontier give witness-slice length≤251655184.
Together these yield the checked uniform1661620381source-body-tick bound
for either real decoded database. Straight-line target work is still separate.

Actual normal whole-builder returns now derive the real table/capacity,
complete physical Patricia image with genuine decoded-record value membership,
count≤1048575, advanced heap, unchanged nonheap globals and protected input.
The original caller's local/clock restoration retains that same result.
The normal capacity proof also covers initial clocks below30 by applying
clock extension to the same observed non-timeout run, not assuming funding.
Main's actual database caller composition/second-table preservation, later
current source paths and uniform target-step composition remain open.

Validation: current-builder-result-frame-v2.log PASS2510jobs, including
complete body/literal decoded-input cost, actual normal result/caller frames
and existing main node trace. Permitted printed axioms only. Index8578modules/
17383facts; inventory8623/replacement closure0/fixed files unchanged. No global
finite target K/full verification. Usage22%weekly/0resetcredits.

## Both real databases and complete main prefix to state_init

The actual node/code scoped callers now cost≤1661620382source ticks apiece
or resume the original continuation with their genuine physical tables and
complete decoded SI/payload/gas/witness context. Every caller's other locals
are retained. Normal results protect all previously allocated memory up to
the actual incoming heap, rather than just main's older root boundary.
A finite-interval Patricia frame and complete prior-result transport prove
that building the code database preserves the already built node database.
Shared header/node/leaf image assembly now lives once in ImageCells; the
older lower-frontier frame reuses it instead of duplicating that proof.

The exact original two-call sequence costs≤3323240764source prefix ticks or
reaches state_init with both images and real nodedb/codedb locals. Composing
the actual header/gas prefix gives≤3374769154source ticks from run_attempt
entry to state_init, or a genuine earlier stop with the original outcome.
The actual afterCodes continuation, final clock and full nonlocal observation
are retained. No future database/state/EVM completion is supplied.

Validation: current-main-to-state-init-v1.log PASS2519jobs, with both database
calls, current main/header/decoder path, exact finite-region image frames,
normal caller data and prior-database preservation. Permitted printed axioms
only. Index8589modules/17396facts; inventory8634/replacement closure0/fixed
files unchanged. No global finite target K/full verification. Usage23%weekly,
0resetcredits. Next: current state_init/decode-witness lookup and later actual
payload/header/EVM source paths, then uniform target-step composition.

## Complete current Patricia lookup cost, normal result and actual caller

The unchanged htab_get120 now costs≤263source body ticks and≤264caller
ticks from an actual32-byte Patricia image. Its actual find-leaf call,
three mapped header loads, four-tick memeq and both result branches are
included, at arbitrary incoming clocks. No mapped/aligned/query-byte-content
premise is required: unreadable query arguments stop within the same bound.

A genuine normal body/caller return is exactly the absent pair or a present
pair whose word belongs to the caller's stored-leaf-value predicate. The
value is read from the actual selected leaf's mapped physical node cell;
its real32-byte query comparison need not be assumed true or successful.
The complete physical state is preserved on all outcomes. Actual lexical
header/comparison scopes and original caller continuations are retained.
This links subsequent nodedb_lookup/MPT decoding to genuine decoded witness
records, rather than arbitrary word addresses or a previous hash-map model.

Validation: current-patricia-get-real-caller-v1.log PASS2532jobs, including
the lookup cost/value/readonly/caller proofs and unchanged full current main
prefix to state_init. Permitted printed axioms only. Index8598modules/
17410facts; inventory8643/replacement closure0/fixed files unchanged. No
global finite target K/full verification. Usage23%weekly/0resetcredits.
Next: current nodedb_lookup record-length contract and state_init/decode path.

## Current database wrapper and genuine bounded witness lookup

The unchanged nodedb_lookup228 now costs≤264source body ticks/265caller
ticks, with all actual present/absent descriptor reads and lexical restores.
A real normal return is absent or gives exactly the pointer and length of
a decoded record stored in the matching current Patricia table. Main's
state_init cut now retains the matching node/code witness images alongside
both physical database results, rather than unrelated existential arrays.
The shared database caller contract derives the found slice's mapped extent,
input boundaries and actual per-record length limit (1024for nodes,65536for
code). It assumes no query bytes, successful lookup or future decoder run.

Validation: current-main-database-lookup-contract-v2.log PASS2538jobs.
Printed axioms permitted only. Index8604modules/17419facts; inventory8649,
replacement closure0/fixed files unchanged. Incremental policy PASS65438
entries/2484982671bytes.
No global finite target K/full verification. Usage24%weekly/0resetcredits.
Next: actual state_init and bounded witness-decoder control flow.

## MPT/RLP cleanup and current bounded root lookup

Moved the identical full-RLP Complete contract into DecodeProgram and reused
it in the current decoder. Existing MPT step/root/state syntax now names
Guest.Software declarations and their actual indices. Removed broad account,
old database and gas-catalogue imports from these syntax/failure helpers; the
root ABI imports its finite-code bridge explicitly. The current decoder reuses
these helpers instead of maintaining a second set of syntax modules.

The actual extension/branch frame suffixes cannot return normally: their
real88-byte scratch allocation is followed by an unmapped store at offset8.
Each suffix costs≤2source ticks, without assuming allocation success. This
is a local cut; full decoder paths must still derive its arena at that point.
The real root comparison handles missing/wrongly shaped empty-root globals
without an extra entry premise. Combining it with the current database gives
a270-tick actual root prefix or a genuine≤1024-byte node witness at the
original continuation, with physical/caller frames retained.

Validation: current-witness-root-lookup-v1.log PASS2553jobs including the
shared syntax/scratch/string/root and complete current main prefix. Permitted
printed axioms only. Index8607modules/17427facts; inventory8652/replacement
closure0/fixed files unchanged. Incremental policy PASS65442entries/
2484995980bytes. Earlier exploratory old-library builds exposed stale imports
and were not indexed. No global finite target K or full verification claimed.
Usage24%weekly/0resetcredits. Continue actual state_init and witness decoding.

## Actual state_init entry, workspace preservation and nibble cleanup

The real main state_init call now derives all three scalar formals from
its observed arguments, including an arbitrary parent-root load or an earlier
stop. Its callee receives the matching decoded node/table images and real
heap frontier; SI locals are not incorrectly assumed to survive the call.
The original40-byte workspace prefix either stops within2source ticks or
reaches its actual root call after three mapped stores. Normal allocation
derives room and the exact ws/heap state without assuming an old ws value.
The older exact-execution helper now states the required persistent room
explicitly instead of confusing it with the larger ordinary-domain bound.

A shared physical table-interval frame and actual workspace-store frame
protect both decoded records and node image. Lookup now consumes that minimal
physical image/code, so unrelated ws/global changes do not invalidate it.
The original completed-builder lookup wrapper remains available.

Retargeted current nibble/key/compact and scalar-node constructors, removed
unrelated trie/gas imports, made code/binding/prefix imports explicit, reused
core strong recursion and removed tactics/order notation imported by accident.
Current key conversion costs≤n/4+3body ticks; compact_to_nibbles≤n/4+6;
scalar node constructors≤2. Their checked global frames retain scratch/frame
cursors. These are local helper facts, not a whole-decoder/global target bound.

Validation: current-state-workspace-and-nibble-cleanup-v5.log PASS2580jobs
including actual main/table/root/state caller/workspace and helper costs/frames.
Permitted printed axioms only. Index8614modules/17437facts; inventory8659,
replacement closure0/fixed files unchanged. Incremental policy PASS65449
entries/2485021520bytes. Usage25%weekly/0resetcredits. No global finite target
K/full verification. Continue actual MPT decode-step/control composition.

## Current caught-parser prefix and real recursive decoder cuts

The actual MPT resolve/decode caught parser now costs≤46*inputLength+14
source ticks on all outcomes. Genuine continuation derives the real parsed
tuple, complete physical frame, caller bindings and original suffix, at a
price≤46*inputLength+13. The real MPT handler cannot manufacture normal
fallthrough; no mapped-scratch/old validation arena is required.

A shared selected-global arena frame proves that actual compact conversion
and node constructors retain main's low scratch/frame cursors despite their
persistent heap updates. The extension path costs≤2ticks and cannot return
a recursive record. The branch's real persistent node constructor,176-byte
clear and scratch suffix cost≤231ticks; its genuine constructor return still
cannot enable the recursive frame. Failure guards and all allocator/store
outcomes remain explicit. The new nullary ABI bridge is shared by the cuts
and cost proofs. Physical witness-row helpers now use their equivalent
pointwise memory frame without importing the old validation proof graph.

Validation: current-mpt-parse-cuts-and-rows-v4.log PASS2558jobs including
current parse prefix, constructor/global frames, branch costs/cuts, row
images and actual main state_init entry. Permitted printed axioms only.
Index8622modules/17455facts; inventory8667/replacement closure0/fixed files
unchanged. Incremental policy PASS65457entries/2485048948bytes. Usage25%
weekly/0resetcredits. No global finite target K/full verification. Next:
current leaf/two-item path and complete witness-decoder loop composition.


## Complete current MPT decode step and physical slice connection

The unchanged Software _decode_step235 now costs at most
`n/4+195*n+284` body source ticks for a genuine at-most1024-byte witness
before the current bounded aligned heap. Its actual caught RLP parser, list
conversion, physical array records, compact-path allocation, second item,
leaf allocation/stores, failure guards and recursive-frame cutoffs are included.
Every genuine normal result has flag zero; extension/branch records cannot
return at main's real scratch/domain configuration. This is the needed local
control fact for bounding the surrounding explicit-stack decoder loop, not yet
a bound for that loop or the whole program.

The converter's own successful return supplies the actual count, item sequence,
allocated rows and next heap. Compact normal returns now retain actual request
room and require the persistent heap ceiling explicitly; ordinary-domain
readability does not imply allocator funding. Removed the old hashmap-region
import from key-byte span proofs, made scope/address imports explicit, and
moved the identical pure slice result into its shared syntax module.

Validation: current-mpt-step-main-regression-v1.log PASS2590jobs, including
actual main/state_init entry and the new decode-step path; all printed axioms
permitted. Index8632modules/17477facts; inventory8677/replacement closure0/
fixed files unchanged. Incremental policy PASS65467entries/2485107882bytes.
No global finite target K/full verification. Usage26%weekly/0resetcredits.
Next: compose the actual witness-body loop and wrappers, then state_init and
later current main paths, followed by uniform target-step composition.


## Complete current witness materialization, root decoding and state_init

The actual _decode_witness_node_body236 costs≤n/4+195*n+287≤200223source
ticks. A genuine normal first decode returns flag zero and sets mode to zero
while retaining top=0; the next iteration disables go. The allowance charges
that final iteration once, instead of multiplying the decode allowance by a
separate large stack bound. Exceptions, bad shapes and short clocks remain
covered. Actual wrapper237 costs≤200225; scratch/catch wrapper238≤200229.

Current decode_witness_to_mpt239 now costs≤200544body source ticks, from
its matching real decoded witness/table images. Actual lookup derives any
present at-most1024-byte input; absence fails at the genuine guard. The real
32-byte hash cache copy and persistent allocation suffix are included.

Complete state_init320 now costs≤200624body source ticks at its actual
main-derived StateInitInputs. Workspace allocation supplies its own40-byte
room; the three actual stores protect earlier witness/table images, and the
real root caller uses the advanced aligned bounded heap. All eight actual
Patricia table constructors, with20/32/52-byte keys, plus the remaining block,
key-scratch and journal allocations cost≤78suffix ticks. No old hashmap is
substituted. Syntax helpers now share current Software declarations/formals
without importing the old witness registry/table runtime graph. Copy32 pricing
uses the core Nat order API explicitly after that import cleanup.

Validation: current-state-init-complete-v2.log PASS2637jobs, including actual
main/state_init entry, full decoder/root and constructor suffix. Printed
axioms permitted only. Index8639modules/17491facts; inventory8684/replacement
closure0/fixed files unchanged. Incremental policy PASS65474entries/
2485159760bytes. Overall estimate remains45%, plausible35–55%, relative to
rebased main; these are local source-cost milestones. No global finite target
K/full verification; claim infinity. Usage27%weekly/0resetcredits.
Next: actual continued main after state_init, its physical/input/global frames,
later execution and uniform target-step composition.


## Main continuation after state_init and shared global effects

The actual run_attempt header/gas/two-database/state-init prefix either stops
within3374969779source ticks or resumes its original afterStateInit suffix.
The same real normal state_init callee return, typed result and saved caller
locals remain explicit for later physical-frame proofs. The state-init caller
allowance is200625ticks; no successful return is supplied as a premise.

A reproducible generator emits one shared global-effect module for the actual
37-function state_init call graph, including all caught handlers. Lean checks
every actual Software code entry and compositional body proof. Only the nine
real destinations bs/heap_ptr/journal/journal_cap/journal_n/scratch_ptr/sk_buf/
ts/ws may change. Actual normal main continuation therefore retains Keccak
state/pad, MPT hash workspace and frame cursor bindings. Scratch restoration,
earlier memory and the returned persistent frontier still need normal proofs.
The generator's --check is nonwriting; source scan alone is not certification.

Validation: current-main-state-globals-v1.log PASS2640jobs/permitted printed
axioms. Generator --check PASS. Index8642modules/17534facts; inventory8687/
replacement closure0/fixed files unchanged. Incremental policy PASS65477entries/
2485266398bytes. Usage27%weekly/0resetcredits. No global finite target K/full
verification; claim infinity. Continue actual normal memory/heap frames and
later main/target-step composition.


## Shared normal persistent frames and complete slice runtime preservation

A shared PersistentNormalFrame retains the genuinely advanced bounded/aligned
heap, all nonheap globals, complete nonmemory runtime metadata and every word
before the entering heap. It composes at actual intermediate frontiers and
survives real call-entry/caller-local/lexical restoration. Current scalar node
constructors and compact conversion now supply this frame from their own
normal allocations. Scalar constructor room is retained explicitly; the
persistent heap ceiling is a real entry fact, separate from ordinary-domain
readability. Node-field proofs no longer import the old hashmap memory-region
graph. Compact writing reuses the shared physical metadata erasure.

The current RLP slice converter now retains its complete runtime metadata
through the actual first pass, allocation, record-writing second pass and
scoped caller. A shared memory-effect rule allows those record writes while
retaining globals, FFI and all other metadata. Existing header/MPT callers
retain their cost/record contracts, with the stronger metadata available.
A real normal converter return now supplies the same persistent frame.

Validation: current-persistent-slices-node-main-v1.log PASS2649jobs, including
current normal node/compact/slice frames, full header/MPT/state-init/main prefix
and globals. Printed axioms permitted only; generator --check PASS.
Index8648modules/17550facts; inventory8693/replacement closure0/fixed files
unchanged. Incremental policy PASS65483entries/2485291692bytes. No global finite target K/full verification; claim infinity.
Usage28%weekly/0resetcredits. Next: normal MPT leaf/step/root/state-init memory
composition, then later main and uniform target steps. Older unused pre-rebase
normal-frame callers still need porting or removal; this is selected current
proof validation, not a successful build of the entire historical Solver tree.


## Complete current MPT decode-step normal frame

The unchanged _decode_step235 now derives its complete normal persistent
frame from the same actual parser/slice/compact/leaf execution. It preserves
all earlier words, all nonheap globals and complete nonmemory runtime state,
with a genuinely advanced bounded/aligned heap. Actual leaf allocation and
both parent-encoding stores stay inside their real fresh node. Source p/n,
compact and value arguments are derived through their actual scoped callers.

The real returned pair names zero or a node at/above the entering heap and
below the persistent ceiling; an arbitrary returned word is not assumed fresh.
This numeric result will protect earlier input from later root-cache stores.
Actual two-item selection excludes normal branch/extension scratch records.
Shared frames now also compose later fresh writes without assuming immutable
memory. Scalar constructor frames retain their actual allocated node region.

Validation: current-step-frame-main-regression-v1.log PASS2655jobs, including
new complete normal decode-step frame and current header/main/state-init costs
and global frames. Printed axioms permitted only. Index8654modules/17564facts;
inventory8699/replacement closure0/fixed files unchanged. No global finite
target K/full verification; claim infinity. Usage28%weekly/0resetcredits.
Next: actual normal witness loop/wrappers/root, followed by state_init's earlier
input/returned-heap frame and continued main/target composition.


## Current witness loop, wrappers and whole root normal frame

The same actual current236 loop now retains its zero/fresh terminal node,
advanced bounded/aligned persistent heap, all nonheap globals, complete runtime
metadata and every earlier word. Current237's catch handler cannot manufacture
successful fallthrough. Current238's genuine mark/release restores the same
scratch cursor on normal return; no successful decode or release is assumed.

Whole unchanged root239 now has that normal persistent frame, including its
real empty-root comparison, physical Patricia lookup, bounded witness decode,
fresh hash-cache allocation/copy and actual node-cache store. A returned node
is zero or lies above the original entering frontier, which protects earlier
input even when that later cache store precedes the latest allocator cursor.
Missing or nonscalar empty-root globals cannot produce a normal return.

The actual state-init workspace prefix now derives room/funding from an
enclosing normal return, and its original root call passes this physical frame
and returned node into the same afterRoot continuation. Shared allocation and
keys/nodes/order metadata frames are independent of the constructor's key width.
Full state-init suffix/input preservation, later main and uniform target-step
composition remain open. No global finite target K; claim infinity.

Validation: current-witness-root-state-main-regression-v2.log PASS2669jobs,
including whole root normal frames, state-init normal root connection and
current main prefix/global proofs. Permitted printed axioms only. Shared
generator --check PASS. Index8665modules/17586facts; inventory8710/replacement
closure0/fixed files unchanged. Incremental policy PASS65500entries/
2485397130bytes. No full verification claimed. Usage29%weekly/0resetcredits.
Continue the actual state-init table/allocation suffix and earlier-input frame.


## Current Patricia constructor frames for every scalar key width

The actual htab_new116 now returns its real fresh header and complete normal
persistent frame for arbitrary scalar key widths, with capacity at least two.
All four allocations derive their own room from the same observed execution;
the actual stride expression, capacity guard and11header stores are retained.
Earlier words, every nonheap global and complete runtime metadata survive,
and the actual final heap remains bounded/aligned and advances monotonically.
No initialized array contents or old hashmap model is assumed.

Reused the current generic array-allocation/store trace and mapped header
stores. A small scalar context/tail composition shares the keys/nodes/order
proof across widths20/32/52 and beyond. Existing32-byte physical Patricia
lookup/insertion contracts retain their separate stronger image guarantees.

Validation: current-table-scalar-normal-v5.log PASS741jobs/permitted printed
axioms only. Index8668modules/17593facts; inventory8713/replacement closure0/
fixed files unchanged. Incremental policy PASS65503entries/2485418086bytes.
No global finite target K or full verification; claim infinity.
Usage30%weekly/0resetcredits. Continue the actual state-init suffix and whole
normal earlier-input/runtime/heap frame, then continued main/target steps.


## Whole current state-init normal memory and retained main inputs

The unchanged state_init320 now has a complete normal execution frame from
its actual main-derived inputs: every word before its incoming heap survives,
all nonmemory runtime metadata is retained, scratch/frame cursors have their
real initialized values, and its actual heap advances within the persistent
ceiling with8-byte alignment. Its normal result is the real scalar zero.

This includes both workspace stores after root decoding, the first scoped
Patricia table, the fresh80-byte block record, all seven later table calls,
all block metadata fields,64-byte key scratch and the actual16MiB journal.
Each allocation's room/funding comes from that same observed execution.
Shared normal memory frames permit the initializer's genuine global writes;
the separately checked effect frame retains its other globals.

The same normal callee return now carries main's SI/payload/gas cells, all
three witness images, hash environments, low arena cursors and advanced heap
into its original afterStateInit continuation. The whole reached-prefix source
allowance remains3374969779. No global finite target K yet; later current main
and uniform target-step composition remain open. Claim infinity.

Validation: current-state-init-returned-main-v2.log PASS2682jobs, including
whole state-init normal memory, retained main inputs and existing cost/global
proofs. Permitted printed axioms only. Index8677modules/17621facts;
inventory8722/replacement closure0/fixed files unchanged. Incremental policy
PASS65512entries/2485471496bytes. No full verification claimed.
Overall effort estimate50%, plausible40–60%, relative to rebased main.
Usage30%weekly/0resetcredits. Next: retain actual payload/transaction record
facts needed after state_init, then transaction scan, payload header/hash,
remaining validation/execution and uniform target steps.


## Retained complete payload image and real transaction budgets

Main's real root-hash return now supplies the complete payload ReturnedImage,
its physical transaction pointer/count/records and already-derived decoder
budgets. The actual transaction count is≤12582752 and aggregate transaction
bytes≤251655056. These facts come from the same snapshot and actual normal
root return; no extra accepted-input hypothesis is introduced.

The current verification Data contract carries that image through actual
header validation, both database builds, global updates and state_init's
normal memory frame. Shared interval/frame transport also retains payload
prefix and remaining fields needed by later header/execution work.

Validation: current-main-payload-data-v2.log PASS2683jobs/permitted printed
axioms only. Index8678modules/17624facts; inventory8723/replacement closure0/
fixed files unchanged. Incremental policy PASS65513entries/2485477092bytes.
No global finite target K/full verification; claim infinity.
Usage30%weekly/0resetcredits. Next: retain the actual pl local through the
existing reached-prefix traces, then prove the original transaction scan.


## Actual payload local and complete current transaction precheck

The same actual header/gas/database prefix now retains pl=the decoded payload
record through every reached lexical action and both database calls. Shared
CallPrefix local preservation uses real checked callee returns/normal commands;
HasTables retains this concrete caller binding for the state-init return.

Current Software run_attempt803's unchanged signed transaction scan costs at
most its actual decoded count≤12582752source ticks on every outcome. The
physical payload image supplies both real pointer/count loads. Failed length
reads, BlockErr4 for empty transactions and short clocks remain covered. Its
normal reached suffix retains SI/pl, complete payload/witness images, gas,
heap and hash workspaces. The whole current main prefix now stops within
3387552531source ticks or reaches its original payload_header suffix with
those actual data and continued execution intact.

Reused the pure guarded-counter proof; removed its accidental reliance on
an imported by_contra tactic and made binding lookup imports explicit. Current
scan syntax/trace helpers use the actual Software declaration and narrow
current state-call syntax, avoiding the older Guest run_attempt graph.

Validation: current-main-transaction-data-v4.log PASS2688jobs/permitted printed
axioms only. Index8682modules/17638facts; inventory8727/replacement closure0/
fixed files unchanged. Incremental policy PASS65517entries/2485499490bytes.
No global finite target K/full verification; claim infinity.
Usage30%weekly/0resetcredits. Next: retire unused pre-rebase alternative path
proofs to recover package entries, then actual payload_header/hash and later
main/execution/target-step composition.


## Retired obsolete alternative path-proof branch

Removed46unused Solver modules (3805lines) rooted at the older
WitnessCorePathInvariant alternative. Its recursive/path state-initialization
branch is superseded by the current actual Software normal-frame proof.
The reverse import closure contains no current proof, and no fixed library or
Solution module imports Solver. All remaining Solver imports resolve.

The retired-original-path-proofs.json manifest records every path/hash/fact
and recovery commit6843032c7. Removed dead module/fact entries from the live
proof index; Git retains their complete history. Kept the separate older
payload-header and generic proof helpers for porting, and preserved all five
pre-rebase untracked WIPs untouched.

Validation: current-main-cleanup-regression-v1.log PASS2688jobs/permitted
printed axioms only. Live index8637modules/17563facts; inventory8681/
replacement closure0/fixed files unchanged. Incremental policy PASS65471
entries/2485195991bytes, recovering room beneath the package entry limit.
No global finite target K/full verification; claim infinity. Continue actual
payload_header/block length/trie/header hash, later main and target steps.


## Current payload-header prefix and dynamic software Keccak pricing

Retargeted the shared payload_header syntax/code entry to actual Software788
and removed its unnecessary gas/old-table catalogue import. The initial
payload-header prefix now costs≤1035source ticks on every outcome, through
all eight real allocations, clears, stores and the ommer hash. The actual
block_rlp_length continuation and reached action execution remain explicit;
an early stopped prefix cannot return a fabricated header.

A current dynamic Keccak caller-price helper covers real pointer/output
expression failures and ABI shapes using the actual44*(bytes/136)+689body
bound. The previous prefix's older Keccak price is no longer used here.
No input mapping, later allocation room or hash success is assumed for cost.

Validation: current-payload-header-prefix-v2.log PASS2694jobs including current
main transaction/data proofs and the current payload-header code environment.
Printed axioms permitted only. Index8638modules/17564facts; inventory8682/
replacement closure0/fixed files unchanged. Incremental policy PASS65472
entries/2485198925bytes. Earlier exploratory catalogue dependency failures
were not indexed; narrowing the actual code-entry import resolves this target.
No global finite target K/full verification; claim infinity.
Usage31%weekly/0resetcredits. Next: derive actual payload/raw/header-buffer
entries and header fields from the retained decoded payload, then compose
block length, real indexed tries and remaining header/main work.


## Actual payload/raw reads and first header-buffer allocation

The retained current Data image now supplies payload_header's real SI/pl/raw
loads and original local scopes at variable actual input/record addresses.
A reached prefix derives its actual fresh248-byte header, first allocation's
request room and full persistent/runtime frame, retaining the unchanged
remaining action execution. Future clear/hash/array successes are not assumed.

Corrected the shared reached-allocation helper's heap premise/room conclusion
to the actual2952790016persistent ceiling. Ordinary-domain readability up to
33806089496cannot establish allocator room. Existing unused older callers
which supplied only that weaker ordinary-domain bound still need porting.

Validation: current-payload-header-entry-v4.log PASS2697jobs, including current
main transaction/data, actual payload_header syntax/code/cost prefix and new
initial read/allocation contracts. Printed axioms permitted only.
Index8639modules/17568facts; inventory8683/replacement closure0/fixed files
unchanged. Incremental policy PASS65473entries/2485205526bytes.
No global finite target K/full verification; claim infinity.
Usage31%weekly/0resetcredits. Next: retain the already-proved copied input
bytes and input/record separation in the payload image, then actual prefix
buffer/header fields and block-length/remaining source/target composition.


## Current copied input and actual header clear/ommer hash

Main now retains the exact copied byte image over the encoded extent,
its aligned pointer and separation before the actual decoded payload
record. The real header/database/state/transaction continuations transport
this image; no future successful read is assumed.

The actual payload_header prefix now derives the full248-byte clear and
first two stores, all31initial header words and earlier-memory protection.
Its next two genuine allocations derive their own32/8-byte room beneath
the persistent ceiling and exact live caller states. The actual one-byte
ommer marker and current24-round software Keccak return retain every real
caller local/global, current workspace, earlier copied input and the new
header. That call costs at most690source ticks. Its original remaining
prefix execution is retained. This does not prove later length/trie/main
work or the final target-step bound.

Validation: current-payload-header-hash-v2.log PASS2704jobs, including main
transaction/data and state-return proofs. Printed axioms permitted only.
Index8643modules/17597facts; inventory8687/replacement closure0/fixed files
unchanged. Incremental policy PASS65477entries/2485243625bytes. Claim infinity; no global finite target K or full verification.
Usage32%weekly/0resetcredits. Next: actual remaining header fields and block
length, indexed tries, remaining main and uniform target-step composition.


## Current header scalar/nonce/base-fee continuation

Connected the actual post-ommer stores, genuine transaction-root allocation,
four-word difficulty zero, all six scalar payload loads/stores, prev-randao
pointer, nonce allocation/clear and actual checked four-word base-fee store.
Main's original continuing prefix now derives the real base-fee values,
earlier-input memory frame and actual next aligned/bounded persistent heap.
A shared allocation-frontier helper now carries the real2952790016ceiling
and derives each reached request's room. The seven hash/clear and scalar
word-store helpers preserve the same original remaining action execution.

Narrowed U256Store's import to its actual WordTupleFour definitions, removing
an unrelated block-length/bit-length proof chain. Added BeStep's missing
explicit BindingLookup import. No Pancake/source/semantics change.

Validation: current-payload-header-basefee-v1.log PASS1898jobs, including
BeStep and the complete new header-prefix chain. Printed axioms permitted
only. Index8647modules/17632facts; inventory8691/replacement closure0/fixed
files unchanged. Incremental policy PASS65481entries/2485298099bytes.
Claim infinity; no global finite target K or full verification.
Usage32%weekly/0resetcredits. Next: retain the decoded SI parent field used
by the remaining stores, complete the root buffers/header fields and connect
actual block length, indexed tries, remaining main and uniform target steps.


## Complete actual header prefix and all physical header words

Retained the decoder's real SI+24parent-root pointer through current main.
Consolidated all decoded input transports into Data.of_interval, replacing
repeated header/database/global/state-return reconstruction with that common
checked memory-frame theorem; the stronger Data contract uses fewer lines.

The current continuing payload_header prefix now derives all eight actual
allocations, all seven auxiliary buffers, all header stores and the genuine
block_rlp_length caller state. Every allocator request's room comes from its
own observed normal return. The actual buffers occupy exactly424bytes from
the incoming aligned heap. All31final header words are checked, including
the genuine base-fee limbs, borrowed input pointers and fresh output pointers.
The decoded/copied images derive all borrowed raw, parent and bounded extra
byte spans, plus input/transaction-array/payload-cell separation before the
real temporary frontier. No later length/trie/hash result is assumed.

Validation: current-payload-header-spans-v1.log PASS2715jobs including actual
main transaction/data/state-return contracts and the complete header chain.
Printed axioms permitted only. Index8650modules/17647facts; inventory8694/
replacement closure0/fixed files unchanged. Incremental policy PASS65484
entries/2485325271bytes. No global finite target K/full verification; claim
infinity. Usage33%weekly/0resetcredits. Next: turn these physical header
facts into actual block-length cost/return contracts, then indexed tries,
remaining main and the uniform target-step theorem. Existing older encoder
helpers still have pre-rebase import/allocator-premise issues to port.


## Physical encoder entry and current U256 allocation contract

Main's actual complete prefix now derives every HeaderEncoding.FieldFacts
premise, the readable header/buffer geometry and the genuine caller frontier,
while retaining the complete decoded Data image at that same block-length
caller. All borrowed spans come from the original copied/decoded input; all
fresh strings come from the eight observed allocations. No later encoder,
allocation, trie or block-length success is a new main hypothesis.

Extracted the unchanged static header field/geometry definitions into the
small shared HeaderEncoding.FieldData module so current input facts do not
import the whole old writer execution library. Removed PutBeProgram's unused
transaction proof import and supplied the writer's actual direct imports.
Ported the U256 writer prepare/whole/caller allocation premise to the real
2952790016persistent ceiling (ordinary mapping remains the wider arena).
The strengthened helper premise must be derived at actual continuing callers;
it is not assumed at main's pre-allocation entry. Fixed a lost two_mul import
with its explicit elementary equality. The Context and all changed writer
modules compile; later old field-run/block helper callers still need porting.

Validation: current-payload-header-physical-v1.log PASS2760jobs, including
current main transaction/state/Data, full header entry and the ported U256
writer/encoder Context. Printed axioms permitted only. Index8652modules/
17650facts; inventory8697/replacement closure0/fixed files unchanged.
Incremental policy PASS65487entries/2485334773bytes. No global finite target K
or full verification; claim infinity. Usage33%weekly/0resetcredits.
Next: bound the actual header encoder/block-length call on every outcome,
deriving any stronger allocation room from its true continuing prefix;
then real indexed tries, later main and the uniform target-step theorem.


## Intrinsic current RLP helper costs and bounded reverse-byte writes

Added a small current RLP catalogue checking21actual software entries,
without the older block-execution/large code catalogue dependency. The
reused shift/reverse-byte loop bodies are proved literally equal to the
actual current Software declarations. Preserved all five earlier untracked
WIPs untouched and unimported.

Current rlp_be_len costs≤8body/9caller ticks and its true normal result is
≤8with every nonlocal retained. The actual reverse put_be loop costs≤its
input count on every outcome, including missing operands, unmapped stores
and exhausted clocks. Its genuine normal return is0and protects every word
outside that counted destination, retaining all runtime metadata/globals/FFI.
Header/word scalar sizers cost≤9body; list-header length≤10body. Their real
normal encoded lengths are1..9and retain all nonlocals even below the
conservative price, by clock padding. Current rlp_write_header costs≤18body/
19caller, deriving its real bounded length-helper return and only pricing
the reverse writer after an actual normal tag store. No mapped-output or
future successful-call premise was added for these cost bounds.

Validation: current-rlp-write-frame-v2.log PASS2052jobs, including the entire
current helper set and actual physical payload-header entry regression.
Printed axioms permitted only. Index8658modules/17683facts; inventory8703/
replacement closure0/fixed files unchanged. Incremental policy PASS65494
entries/2485376634bytes. No global finite target K/full verification; claim
infinity. Usage34%weekly/0resetcredits. Next: header/byte/word/wide writer
normal frames and intrinsic costs, actual full encoder/block-length bound,
then indexed tries, later main and uniform target steps.


## Current header-writer normal frames and genuine caller memory

Added bounded-span inclusion and actual ignored-caller frame transport.
The current put_be caller now retains its genuine callee's counted memory
frame and complete nonlocal state. Fixed IgnoredCallTarget's missing explicit
Guest.Model import, exposed by the narrowed dependency closure.

The actual current rlp_write_header normal return now derives its true
encoded length1..9, full runtime/global/FFI preservation, write confinement
to the nine-byte destination span and the already-proved≤18body source cost.
Both real short-tag and long-length paths are checked. The long path derives
its actual byte-count child, normal tag store, ignored reverse-byte return,
restored ll binding and final returned length from that same execution.
No output mapping, later funding or successful helper is assumed in advance.

Validation: current-rlp-header-frame-v1.log PASS731jobs; printed axioms
permitted only. Index8659modules/17690facts; inventory8704/replacement
closure0/fixed files unchanged. Incremental policy PASS65495entries/
2485391301bytes. No global finite target K/full verification; claim infinity.
Usage34%weekly/0resetcredits. Next: compose current word/byte/wide writers
and complete actual header-encoder/block-length bounds, then indexed tries,
later main and uniform target steps. Five old untracked WIPs remain untouched.


## Current scalar-word and byte-string encoder contracts

A shared short-tag guard now preserves the actual real returning path.
Current rlp_encode_word costs≤18body/19caller source ticks on every outcome,
including both zero/single-byte early returns and the long form. Its true
normal result is1..9with bounded nine-byte writes and all nonlocals retained.

Current rlp_encode_bytes now derives all byte/header/copy accesses from
owned source/destination spans, as supplied by the actual earlier header
entry. It costs≤length+20body/+21caller on every entry clock and its genuine
normal return is at least both1and length, at most length+9, and retains all
nonlocals while writing only that bounded destination. Empty and single-byte
special cases are included. These range premises describe the caller's
proved earlier allocations; no later return or allocation success is assumed.
The permitted helper entries come only from the current software catalogue.

Validation: current-rlp-bytes-write-v2.log PASS2063jobs, including the current
scalar/length helpers and actual physical-header entry. Printed axioms
permitted only. Index8661modules/17705facts; inventory8706/replacement
closure0/fixed files unchanged. Incremental policy PASS65497entries/
2485410097bytes. Claim infinity; no global finite target K/full verification.
Usage34%weekly/0resetcredits. Next: current wide writer, actual complete
encoder/block-length bounds, indexed tries, later main and uniform target steps.


## Current wide-integer writer: all outcomes and own allocation room

Current rlp_put_u256 now has a checked124body source-clock bound for every
outcome at a valid earlier output span and bounded persistent heap. A32-byte
request that cannot fit stops within3body ticks. A genuine normal execution
proves that its own actual allocator accepted that request; future room is
not a caller hypothesis. Its true encoded length is1..41, with complete
nonlocal preservation and writes confined to output41plus temporary32bytes.
All helper identities are tied to the actual current Software catalogue.

Validation: current-rlp-wide-write-v5.log PASS2082jobs, including scalar
helpers and physical-header regression. Printed axioms permitted only.
Index8662modules/17715facts; inventory8707/replacement closure0/fixed files
unchanged. Incremental policy PASS65498entries/2485424629bytes. Claim
infinity; no global finite target K/full verification. Usage34%weekly,
0resetcredits. Next: compose the complete actual header encoder and block
length; indexed tries, remaining main and uniform target steps still open.


## Current header fields compose without future-success premises

Every literal header field now derives its actual call arguments from the
retained header cells. The assigned writer costs its own allowance on every
outcome, and a real normal return derives its encoded length, saved caller
locals, current heap and protected older memory. The real pointer advance
then establishes the next bounded natural output position. Literal field
lists compose these facts and prices only along their actual normal prefix;
aborted fields never invoke a later-field contract. Both wide fields and
the optional fields use the same checked composition.

Narrowed ListWrite and SuffixArithmetic imports: the already-proved final
list-header suffix no longer imports unrelated whole-header field execution.
No program or semantics changed. Validation: current-rlp-header-fields-v1.log
PASS2087jobs; current-rlp-suffix-imports-v1.log PASS2092jobs. Printed axioms
permitted only. Index8664modules/17726facts; inventory8709/replacement
closure0/fixed files unchanged. Incremental policy PASS65500entries/
2485449386bytes. Claim infinity; no global finite target K/full verification.
Usage35%weekly/0resetcredits. Next: complete the actual header encoder and
block length, then indexed tries, remaining main and uniform target steps.


## Complete unchanged current header encoder

The complete current Software encode_header is now checked against its
actual catalogue entry. All outcomes, including a failed output allocation
or later wide temporary request, cost at most1346body source-clock ticks.
The1024-byte allocation room is derived only from that same allocator's
actual normal return. The first field, all20remaining base fields, the
current-header optional pair and the final list header compose directly.

Any genuine normal return derives a length1..916and a mapped output span,
the real heap cursor after the1024-byte output allocation, all other
nonlocal metadata and every older header/input cell. Strengthened the shared
suffix with output-span ownership and retained its previous theorem as a
compatibility projection. No executable bytes or semantics changed.

Validation: current-rlp-header-encoder-v1.log PASS2097jobs with physical
payload-header regression. Printed axioms permitted only. Index8669modules/
17749facts; inventory8714/replacement closure0/fixed files unchanged. No
global finite target K/full verification; claim infinity. Usage35%weekly,
0resetcredits. Next: current block-length composition, indexed tries,
remaining main and uniform target steps.


## Block-length tails cover the current allocator-derived input budget

The transaction size/step/loop/phase contracts now cover slices up to
251655056bytes, replacing the historical134217712-byte premise. The pure
byte-size arithmetic remains nonwrapping; the generic transaction encoded
sum cap is817878932. The reached block tail still costs≤12*txCount+
43*withdrawalCount+33source ticks and derives its genuine returned word,
withdrawal lower bound and pure state frame. Its generic encoded upper cap
is817879876+57*withdrawalCount. This is a size cap, not the runtime bound.

Moved code-frame transport beside its code structures and narrowed the old
memory-frame import. The actual current tail can now be imported without
the unrelated historical whole-header execution proof. Added the missing
explicit HeapFrame import at the withdrawal scalar proof. No program or
semantics changed. Historical WholeBlock/BlockCurrent wrappers have not been
retargeted and are not claimed checked; the new current composition follows.

Validation: current-rlp-block-tail-v2.log PASS2123jobs, including the complete
current encoder and physical-header regression. Printed axioms permitted
only. Index8669modules/17749facts; inventory8714/replacement closure0/fixed
files unchanged. No global finite target K/full verification; claim infinity.
Usage35%weekly/0resetcredits. Next: actual current block-length call and
physical caller, indexed tries, remaining main and uniform target steps.


## Complete unchanged current block_rlp_length

The actual current block-length entry now has an all-outcome source-clock
bound12*txCount+43*withdrawalCount+1382. It includes the real heap mark,
complete header encoder, heap release, both decoded length loops and final
list headers. The header's own1024-byte and wide-temporary allocation room
is derived from those same actual normal calls, never assumed by the caller.

A genuine normal block-length return derives its exact nonwrapping word,
25*withdrawalCount lower bound, generic817879876+57*withdrawalCount upper
bound, original restored heap/all runtime metadata and protected older
input/header memory. All required code/ABIs are tied to current Software
entries. The physical decoded input contract is still explicit; connecting
it to the reached payload_header prefix is the next step.

Validation: current-rlp-block-length-v2.log PASS2128jobs with physical-header
regression. Printed axioms permitted only. Index8674modules/17762facts;
inventory8719/replacement closure0/fixed files unchanged. Incremental policy
PASS65510entries/2485518288bytes. Claim infinity; no global finite target
K/full verification. Usage35%weekly/0resetcredits. Next: derive block data
at the actual caller, then indexed tries, remaining main and uniform target
steps. Five historical untracked WIPs remain untouched/unclaimed.


## Actual main-derived block-length caller and retained physical return

The retained current decoder evidence now supplies every block-length
input: copied bytes, decoded transaction records, withdrawal range/count,
and actual mapped payload cells. The allocator frontier implies encoded
input≤251655056, transactionCount≤12582752and withdrawalCount≤5719433;
the mathematical input list remains unrestricted. Narrowed the pure
withdrawal arithmetic module's imports to its actual prerequisites.

The real current payload_header block-length call either stops within
396930026source-clock ticks or reaches its actual next caller within that
allowance. This includes the396930025uniform callee-body bound. Any actual
normal return derives its true size, restored heap and protected older
memory. A generic metadata/earlier-memory transport and the header-return
proof retain the complete physical header, input, transaction and witness
contracts at that resumed caller, ready for the actual size guard and tries.

Validation: current-block-returned-v1.log PASS2135jobs. Printed axioms
permitted only. Index8679modules/17771facts; inventory8724/replacement
closure0/fixed files unchanged. Incremental policy PASS65515entries/
2485539481bytes. Claim infinity; no global finite target K/full verification.
Usage36%weekly/0resetcredits. Next: actual guard/trie entry and indexed tries,
then remaining main and uniform target steps.


## Actual size guard and complete payload-header prefix to indexed tries

Every actual outcome of the unchanged payload_header now either stops
within396931061source-clock ticks, without a normal header return, or
reaches its genuine first indexed-trie caller within that price. The
reached caller retains the complete physical input/header/witness contract.
Its actual block-length result is nonwrapping, and the real original8MiB
size guard derives encoded≤8388608and withdrawalCount≤335544. No future
trie, guard or helper success is assumed; the guard proof needs no exception
shape premise. Added exact current-callee transport for reached scoped calls.

Validation: current-payload-trie-entry-v2.log PASS2140jobs. Printed axioms
permitted only. An earlier pair of checks briefly overlapped and collided
in the build cache; both failed logs are unclaimed, and the final single
clean build covers their affected dependency closure. Index8682modules/
17777facts; inventory8727/replacement closure0/fixed files unchanged.
Incremental policy PASS65518entries/2485551402bytes. Claim infinity; no
global finite target K/full verification. Usage36%weekly/0resetcredits.
Next: retarget/reuse the original pure trie insertion proofs and construct
actual indexed-trie invariants, then remaining main and uniform target steps.


## Shared RLP catalogue retargeted to current Software declarations

The21legacy shared RLP lookup proofs now use actual current function
positions and declarations, including wide209/header210/withdrawal778/
block787. Each proof checks the unchanged helper body against that real
current declaration. Removed the historical whole-block guard dependency
and the unrelated EVM/dictionary execution imports; code records now come
from the checked current encoder/block helper structures.

Added a reproducible named-file retargeting/check tool. It changes lookup
proofs only and leaves all executable declaration/body definitions alone.
Validation: current-rlp-catalogue-v2.log PASS2141jobs with the complete
payload-to-trie regression; retargeting --check PASS. Printed axioms
permitted only. Index8682modules/17777facts; inventory8727/replacement
closure0/fixed files unchanged. Policy PASS65518entries/2485552391bytes.
Claim infinity; no global finite target K/full verification. Next: pure
insertion helpers/actual indexed-trie models, remaining main and target steps.


## Current pure trie insertion iteration and dependency cleanup

Retargeted the insertion/leaf/split/prefix/invalidation/walk lookup proofs
to actual current Software positions. The original insertion traversal
iteration now checks at≤565source-clock ticks on every outcome using only
its actual six scalar operands, current level≤key length≤64and installed
code. Leaf replacement/splitting, current common-prefix and byte equality,
branch/extension constructors, failed reads/allocations and short clocks are
included. This is the iteration allowance; the full current indexed-loop
invariant and iteration count remain to be connected.

Separated literal iteration prefix/footer, branch syntax and scalar call
ABI facts from normal graph-mutation outputs. Narrowed field-store and
walk imports; the cost dependency set fell from832to roughly200Solver
modules and no longer imports the removed hash-table lookup implementation.
Moved shared facts retain their previous names for normal graph clients.
Fixed exposed missing explicit dependencies and reflexive/Nat comparison
proofs. No executable declaration/body or fixed-source file changed. The
older normal graph/constructor clients are still pending current checks.

Validation: current-trie-insert-iteration-v6.log PASS2203jobs, with the
current walk declaration and complete payload-to-trie regression. Printed
axioms permitted only. Index8683modules/17777facts; inventory8728/
replacement closure0/fixed files unchanged. Policy PASS65519entries/
2485553664bytes. Claim infinity; no global finite target K/full verification.
Usage37%weekly/0resetcredits. Next: actual allocator-derived normal trie
frames/loop invariant, indexed builder, remaining main and target steps.


## Complete current insertion loop and actual normal tree output

The unchanged current _mpt_insert_node249 now checks at36790body source
clocks on every outcome. The actual normal iteration either clears go or
strictly advances the consumed key length; its rank allows at most65iterations.
A genuine normal full insertion returns a registered root and derives the
real evolving heap, preserved older words/tags, bounded values, path bytes,
node/path separation and protected query storage for subsequent insertions.
This is a local physical-entry theorem, not yet the whole indexed builder.

Actual normal bounded allocations now derive their own persistent room from
the observed guards plus no-wrap supplied by earlier ordinary ownership.
Scalar/branch constructors retain their complete actual field writes and
older memory; ordinary rounding geometry is separate from persistent guards.
No future allocation or successful graph output is an entry hypothesis.

Separated shared region geometry, key-width data and scratch/graph frame
facts from retired hash-map, accelerator and parser execution dependencies.
Restored explicit normal-helper imports after the earlier cost-only cleanup;
updated small natural-comparison and field-distinctness proofs. Compatibility
exports retain their old names. Fixed program/semantics/ROM files unchanged.

Validation: current-trie-node-cells-v3.log PASS2149jobs;
current-trie-physical-cleanup-v5.log PASS2199jobs;
current-trie-insert-normal-v3.log PASS2394jobs, including the current complete
payload-to-trie regression and shared region compatibility module. Printed
axioms permitted only. Index8686modules/17783facts; inventory8731/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K or
full verification. Next: current unsecured key/setter and actual indexed-loop
invariant, remaining main and target-step composition. Five historical
untracked RLP WIPs remain untouched/unclaimed. Usage38%weekly/0resetcredits.


## Current unsecured indexed-key conversion and whole setter allowance

The actual current mpt_nibble_key244 unsecured branch costs≤length/4+6,
thus≤14body source ticks at a key of at most32bytes. A true normal call
derives its fresh2*length-byte nibble span, exact heap/runtime metadata,
saved caller locals and complete earlier-memory frame. The bounded real
allocation derives persistent room from its own checked guard and earlier
no-wrap, without an assumed successful future request.

Its actual reached caller now reconstructs the retained graph, values,
path bytes/separation and protected query at the new heap. This current
unsecured path imports no cryptographic oracle. The real mpt_set call now uses its checked current catalogue position
(the insertion child is249); its whole body costs≤36806source ticks on every outcome for
a nonempty row and fresh unsecured indexed-trie entry. Normal key conversion
supplies the true insertion query before the suffix is priced. Row nonemptiness
is an explicit local entry condition; deriving it from the actual main scan
and connecting the whole indexed loop remain open, not global hypotheses.

Validation: current-unsecured-key-v3.log PASS2408jobs;
current-indexed-set-prerequisites-v1.log PASS2426jobs;
current-indexed-set-entry-v1.log PASS2214jobs;
current-indexed-set-cost-v1.log PASS2427jobs with complete payload-to-trie
regression. Printed axioms permitted only. Index8689modules/17788facts;
inventory8734/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verification. Next: actual setter normal
frame, indexed-loop invariant and main-scan nonemptiness, then remaining
main and target-step composition. Usage38%weekly/0resetcredits.


## Actual main scan establishes nonempty rows; complete setter normal output

The current unsecured indexed setter now has its full normal-output theorem:
its actual key conversion, insertion, root store and lexical exits return0,
a registered root, the real monotone aligned heap and retained node/value/
path geometry. Every earlier word below the original cutoff survives except
the map's own root cell; all nonheap globals remain fixed. The original
nonempty-row entry condition is still explicit for this local setter proof.

The real current run_attempt transaction scan now discharges that condition
for transactions. A normal guard reads a nonzero length even without assuming
a valid exception shape. The real signed counter visits every decoded row;
its successful exit proves the pure TransactionsNonempty input fact for all
original decoded record lengths. Actual record-cell ownership supplies its
read interface. Main's complete prefix now carries that fact to the genuine
afterTransactionScan continuation within the same3387552531source allowance.
No input validity or later trie success is assumed to derive the fact.

Validation: current-indexed-set-normal-v4.log PASS2429jobs;
current-transaction-nonempty-v2.log PASS2685jobs;
current-main-transaction-nonempty-v2.log PASS3063jobs, including complete
payload-to-trie and insertion/setter regression. Printed axioms permitted
only. Index8691modules/17793facts; inventory8736/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verification.
Next: actual current indexed-loop entry/key workspace and repeated-row
invariant, then remaining main and target-step composition. Usage38%weekly/
0resetcredits. Five historical untracked RLP WIPs untouched/unclaimed.


## Actual indexed-key workspace and current repeated-row model

The actual mpt_init allocation now establishes mpt_key_scratch2701134808,
with its16-byte span ending at2701134824before the copied input. Shared
all-outcome startup/decoder/hash frames preserve that global. The real main
input contract retains it through header validation, both current Patricia
databases, state initialization and the physical payload-header/trie caller.
The generator sources and reports were updated reproducibly and rechecked.

The current indexed-loop model has no obsolete secure-hash oracle, historical
workspace constants or historical scratch-arena hypothesis. It carries actual
nonempty decoded rows before its header, live registered nodes/path buffers
after its aligned cutoff, true root/flag cells, current key global and heap.
Actual RLP key returns cost≤19caller ticks, derive encoded1..9and preserve
all loop data/rows. The actual ignored setter costs≤36807caller ticks and
its real normal return supplies the new graph, heap and retained rows/header.
The normal sixteen-byte mpt_new constructor now derives persistent room from
its own actual normal allocation, and its lookup plus the indexed program
lookup are tied to current Software declarations. The complete repeated loop
and builder/root suffix still remain open.

Validation: current-indexed-key-workspace-v1.log PASS3063jobs;
current-indexed-loop-model-v2.log PASS3072jobs, including actual current main
transaction-nonemptiness, physical payload-to-trie, setter and constructor
regressions. Printed axioms permitted only. Both generator --check runs PASS.
Index8693modules/17802facts; inventory8738/replacement closure0/fixed files
unchanged. Claim infinity; no global finite target K/full verification.
Usage39%weekly/0resetcredits. Next: bound/retain the actual repeated indexed
loop, constructor/root suffix and actual main caller; remaining main and
uniform target steps follow. Five old untracked RLP WIPs untouched/unclaimed.


## Complete current indexed loop and real transaction-array entry

The complete unchanged indexed loop now costs at most36827*count source
ticks on every outcome, with36826body ticks per iteration. At the actual
derived transaction-count cap12582752 this is463385007904source ticks.
Normal iteration and loop exits retain the actual root, registered graph,
rows, monotone aligned heap, nonheap globals and older input memory; the
final counter equals the original count. The constructor prefix derives its
own successful allocation room and initializes the fresh empty loop model.
The full builder now stops within36827*count+4or reaches its genuine final
root-calculation suffix. That suffix is still open; this is no whole-builder
or global target bound.

The actual physical payload-header prefix now retains its four scoped root
destinations. The real decoded transaction records, original successful
nonempty scan and current bounded heap instantiate the indexed builder's
complete entry, including its literal evaluated arguments and current code
lookup. No successful future trie or allocation is assumed. Ordinary rounding
geometry is separated from persistent allocation guards in shared setup.

Validation: current-indexed-loop-v1.log PASS3073jobs;
current-indexed-setup-v2.log PASS3078jobs;
current-header-root-locals-v1.log PASS3078jobs;
current-indexed-transactions-v4.log PASS3079jobs, including current main
transaction data and payload-to-trie regressions. Printed axioms permitted
only. Index8696modules/17815facts; inventory8741/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verification.
Usage40%weekly/0resetcredits. Next: actual root calculation/cache evidence,
remaining main and uniform target-step composition. Five historical untracked
RLP WIPs remain untouched/unclaimed.


## Real cache mutation facts and current leaf insertion outputs

Added a separate zero-cache preservation contract, without requiring an
arbitrary decoded graph to start uncached. Real node allocation separation
proves that structural/value/child stores cannot alias cache8or24; actual
invalidation stores preserve zero caches and clear the visited node's caches.
Real scalar and branch constructors derive empty caches directly from their
checked field writes. These facts concern actual memory, with no new oracle
or unproved global hypothesis.

The current two-leaf branch builder now returns its genuine branch with
empty caches, through both real side stores and caller restoration. Leaf
splitting returns an uncached branch or fresh extension. Matching-leaf
replacement preserves existing zero caches; the complete current leaf helper
and assigned caller retain zero caches across all old graph nodes and return
an uncached root whenever the visited leaf was uncached. Shared extension-side
outputs also retain the cache frame. The complete insertion-loop/root cache
connection is still open; no whole-builder or global runtime bound is claimed.

Validation: current-trie-two-leaf-cache-v1.log PASS1193jobs;
current-trie-leaf-split-cache-v1.log PASS1229jobs;
current-trie-leaf-normal-cache-v1.log PASS1269jobs;
current-trie-cache-leaf-regression-v2.log PASS3080jobs, including actual current
main transaction data, indexed loop/setup and payload-to-trie regressions.
Printed axioms permitted only. Usage41%weekly/0resetcredits. Claim infinity;
no global finite target K/full verification. Next: complete extension splitting
and insertion-loop cache evidence, actual root calculation, remaining main and
uniform target-step composition. Five historical RLP WIPs untouched/unclaimed.


## Current extension splitting derives its empty root caches

The real old/new extension-split side outputs now carry zero-cache
preservation through their fresh constructors, child/value stores, declarations
and caller restoration. The whole current _split_extension normal call returns
its actual fresh branch with empty RLP/hash caches. The insertion's actual
optional extension wrapper likewise derives an uncached returned branch or
fresh extension. This strengthens actual output evidence and assumes no future
success or empty cache in an arbitrary input graph. The complete insertion
loop still must retain its selected root's cache fields across later iterations.

Validation: current-trie-extension-cache-v1.log PASS1223jobs;
current-trie-extension-cache-regression-v1.log PASS3080jobs, including actual
main transaction data, current indexed loop/setup and payload-to-trie regression.
Printed axioms permitted only. Claim infinity; no global finite target K/full
verification. Usage41%weekly/0resetcredits. Next: full insertion/root cache
connection, actual root calculation, remaining main and uniform target steps.


## Whole insertion and actual indexed loop now retain empty root caches

The actual insertion dispatch now derives its uncached visited node from
the real node_invalidate call. Every actual terminal or descent output retains
zero caches in old nodes and supplies its genuine uncached selected root. The
parent child-slot store is separated from every cache field by the current
graph geometry. The actual loop initializes its result to zero and preserves
the selected root's empty RLP/hash caches through all later iterations, lexical
exits, final return and assigned caller. No empty-cache premise is imposed on
the incoming graph.

The complete current setter then preserves those real empty root caches
through the root-header store and both call scopes. The indexed builder's
RLP key writes preserve them by actual workspace/node separation. Constructor
setup, repeated rows and normal final loop exit now carry that same uncached
root as checked execution evidence. This closes the previously missing cache
invariant, but pricing/executing the actual final root suffix remains open.

Validation: current-trie-cache-dispatch-v1.log PASS1325jobs;
current-trie-cache-whole-insert-v1.log PASS1373jobs;
current-indexed-root-cache-v1.log PASS3080jobs, including actual main transaction
data and payload-to-trie regressions. Printed axioms permitted only. Claim
infinity; no global finite target K/full verification. Next: current root
calculation, remaining main and uniform target-step composition.


## Current uncached root calculation and actual normal output

The actual _node_rlp_fill258 now stops within2body source ticks at the
real startup scratch/frame cursors: after its mark and48-byte scratch
allocation, its first frame store is below the actual ordinary memory domain.
Every clock and outcome is covered, with no assumed successful future helper.
At an actual uncached node, current node_rlp259 stops within3body ticks and
node_hash264 within4; no actual normal return can reach their later encoder,
allocation or Keccak suffixes.

Current mpt_root265 now costs≤5body ticks from its physical local entry,
covering both the owned32-byte empty-root copy and uncached nonempty root.
Any actual normal root return selects the empty-root branch, returns0,
retains all nonlocal metadata and preserves every word outside its actual
output span. This is still a local entry theorem: the builder/root caller
must connect the saved output local, original empty-root buffer global and
retained startup arena to the reached suffix before claiming a whole builder.

Consolidated the new scratch/encoder/hash/root proofs into one helper module
to save a package entry. Fixed an exposed reflexive Nat comparison in the
existing pure copy-cost lemma. Fixed executable/ROM/semantics unchanged.
Validation: current-trie-root-consolidated-v1.log PASS3084jobs, with current
indexed setup, actual main transaction data and payload-to-trie regressions.
Printed axioms permitted only. Index8698modules/17840facts; inventory8743/
replacement closure0/fixed files unchanged. Claim infinity; no global finite
target K/full verification. Usage42%weekly/0resetcredits. Next: actual complete
indexed-builder/root caller, remaining main and uniform target steps.


## Complete unchanged indexed builder allowance, including its final root

The unchanged build_mpt_indexed266 now costs≤36827*count+11body source
ticks on every outcome, from its actual row/heap entry and owned startup/output
buffers. At count≤12582752this is463385007915body ticks. The final root call,
heap release and return cost≤7; the constructor/prefix and complete repeated
loop are included. The original output local and heap mark are derived from
the real prefix and preserved by the actual loop syntax and normal exit.

This is a complete local helper bound, not yet a whole-main bound. Main must
still supply the actual empty_trie_root global and output-buffer contract at
its first transaction-trie call, then retain its genuine normal continuation.
The root proof already excludes normal returns from uncached nonempty roots;
showing that positive row counts actually return nonzero roots is an additional
reachability fact still to prove, before using it to prune later main work.

Validation: current-indexed-whole-cost-v3.log PASS1621jobs;
current-indexed-whole-regression-v1.log PASS3084jobs, including actual main
transaction data and payload-to-trie regression. Printed axioms permitted
only. Index8698modules/17846facts; inventory8743/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verification.
Usage43%weekly/0resetcredits. Next: actual startup empty-root buffer/main
caller, normal builder reachability and remaining main, then uniform target
steps. Five historical RLP WIPs remain untouched/unclaimed.


## Main derives the empty-root buffer and complete first trie allowance

The same actual mpt_init startup now establishes empty_trie_root2701134640
and its32-byte ordinary span. Shared startup/decoder/hash frames retain its
global, and main's real decoded input contract carries it through header
validation, both databases, state initialization and the physical payload
header. The existing transaction-root allocation supplies the actual output
span. Both generator sources/reports were updated and --check passes.

The literal first transaction-trie call in payload_header now derives every
complete builder condition from that same prefix and successful original scan.
Its full ordinary caller allowance is463385007916source ticks, on every
outcome; no empty-root-buffer oracle or later helper success is supplied.
Actual normal builder continuation and the remaining main path are still open.

Validation: current-startup-empty-root-v1.log PASS1600jobs;
current-main-indexed-cost-v1.log PASS3084jobs, including actual main transaction
data, current complete indexed builder/root and payload-to-trie regressions.
Printed axioms permitted only. Index8698modules/17850facts; inventory8743/
replacement closure0/fixed files unchanged. Claim infinity; no global finite
target K/full verification. Usage43%weekly/0resetcredits. Next: prove positive
row counts produce nonzero roots, derive actual normal builder continuation,
then remaining main and uniform target-step composition.

## Normal current indexed returns force zero rows

Every real successful insertion now proves a nonzero returned root, through
leaf/extension construction, dispatch, parent stores and the complete actual
loop. The assigned insertion and setter retain that fact. The current indexed
loop derives a nonzero final root whenever it processes a row; no new global
hypothesis or future successful helper is supplied.

Combining this with the checked current mpt_root semantics proves that any
normal whole build_mpt_indexed return has count zero. Its same actual execution
returns zero, restores the original saved heap pointer, retains every other
global and preserves older memory outside its owned 32-byte root output. All
outcome costs continue to cover nonempty inputs, failures and short clocks.

Validation: current-indexed-normal-frame-v2.log PASS2705jobs, including the
literal first transaction-trie caller; printed axioms permitted only. Index
8698modules/17853facts; inventory8743/replacement closure0/fixed files unchanged.
Incremental policy65534entries/2485762167bytes. Claim infinity; no global finite
target K or full verifier success. Usage43%weekly/0resetcredits. Next: actual
main transaction continuation and withdrawals/header suffix, remaining main,
then uniform target-step composition and final cleanup.

## Actual main reaches the withdrawal suffix with zero transactions

The complete current builder normal contract now also retains all nonlocal
metadata after its saved heap is released. The literal transaction-trie caller
uses that same observed return to retain PhysicalHeader (all input data,
31 header cells, four root-buffer locals and the original heap frontier) and
derive the actual decoded transaction count zero. A generic physical-header
transport covers later writers beyond those header cells. The actual whole
payload-header trace through this caller either stops or reaches its unchanged
withdrawal suffix within463781938977source ticks. The prior block-size and
withdrawal-count guard facts remain live. No future helper return is assumed.

Validation: current-main-after-transaction-v2.log PASS2707jobs; permitted
printed axioms only. Index8698modules/17856facts; inventory8743/replacement
closure0/fixed files unchanged. Incremental policy65534entries/2485773208bytes.
An existing AllocatedAwayBelow helper needed its explicit CopyGeneralMemory
import after the earlier foundation cleanup; its proof now checks. Claim
infinity; no global finite target K/full verifier success. Usage44%weekly/
0resetcredits. Next: withdrawal encoder/loop and trie, rest of payload_header
and main, uniform target steps, final cleanup.

## Current withdrawal input, allocation and address-size foundations

The literal unchanged withdrawal prefix/loop shapes now check against
SoftwareAst. Main's retained decoded payload supplies the actual count read
and every owned44-byte record before the original input boundary. The actual
wd_rlp_slices global-result allocation costs at most2source ticks; its same
normal return derives its own checked persistent room, owned array extent
and exact heap/global update, without an assumed initial destination binding.
The reusable allocator normal helper includes invalid global destinations.

The current RLP writer now also derives the exact21-byte encoded size of a
20-byte withdrawal address from its actual header/copy/return path. This
sharper normal size is needed to prove the existing64-byte buffer sufficient;
the program and buffer size remain unchanged. Complete withdrawal writer,
loop and trie, later header/main and uniform target composition remain open.

Validation: current-withdrawal-prefix-v4.log PASS2709jobs, including rebuilding
startup/main users of the allocator helper; printed axioms permitted only.
Index8700modules/17864facts; inventory8745/replacement closure0/fixed files
unchanged. Incremental policy65536entries/2485790287bytes: package entry cap
is now exactly full; consolidate or remove an unused module before adding
another path. Claim infinity; no global finite target K/full verifier success.
Usage44%weekly/0resetcredits. Five historical RLP WIPs remain untouched.

## Current withdrawal list finisher and actual loop-entry trace

The actual rlp_finish_list ABI/body now has a complete execution proof for
an owned64-byte buffer at any real payload end position9..57. The actual
length helper, overlap-safe memcpy, list-header writer, return and lexical
restoration all occur in this execution. Its output length is1..57; writes
remain within the same64-byte buffer, metadata are retained, and every
outcome costs at most100body source ticks (short clocks included). The normal
contract uses clock padding of this actual body, with no future success
hypothesis. This is a local helper allowance, not a global target bound.

The unchanged withdrawal count/global-array/counter prefix also now has a
complete two-source-tick trace: it either stops or reaches its actual encoding
loop with the same continuation after those three actual actions. Complete
withdrawal encoding/loop/trie and the rest of header/main remain outstanding.

Validation: current-withdrawal-loop-entry-v1.log PASS2709jobs; permitted
printed axioms only. Index8700modules/17872facts; inventory8745/replacement
closure0/fixed files unchanged. Incremental policy65536entries/2485808244bytes
(entry cap full). Claim infinity; no global finite target K/full verifier
success. Usage44%weekly/0resetcredits. Next: combine current word/byte/list
writer contracts into the unchanged withdrawal encoder, then its loop and
indexed trie, remaining header/main and uniform target steps. Cleanup remains
on the plan; historical five RLP WIPs are untouched/unclaimed.

## Complete current withdrawal encoder cost

The unchanged encode_withdrawal_rlp (current779) now has a complete201-body-
source-tick all-outcome bound. Its own genuine alloc64 capacity check derives
buffer ownership; each of the three actual word writers reads the same older
44-byte input record, and the address writer derives its exact21-byte size.
Real caller restoration and p=p+w updates retain the input image and buffer
context. The final actual list helper and pair return are included. No future
allocator, writer or normal suffix is assumed; failed allocations, malformed
destinations, stopped helper calls and short clocks are covered.

Reusable same-run normal word/address/advance/final-list contracts also retain
all input bytes and bounded writes. The whole encoder's composed normal-return
contract and the surrounding withdrawal loop/trie are next; the global target
bound, remaining header/main and final cleanup are still outstanding.

Validation: current-withdrawal-encoder-cost-v2.log PASS2709jobs; permitted
printed axioms only. Index8700modules/17892facts; inventory8745/replacement
closure0/fixed files unchanged. Incremental policy65536entries/2485844740bytes
(entry cap full). Claim infinity; no global finite target K/full verifier
success. Usage45%weekly/0resetcredits. Five historical RLP WIPs untouched.

## Whole current withdrawal encoder normal result

The same genuine current779 normal return now supplies its actual pair:
the freshly allocated incoming heap pointer and an encoded length1..57.
The full seven-command field prefix is extracted from that run; real scalar
calls, the exact21-byte address result, assignments and final list helper
supply every intermediate buffer position. The original64-byte allocation
is derived from its own capacity check. Its precise allocation metadata is
retained, and all memory outside that64-byte span is unchanged. No normal
later call or output-memory oracle is an entry premise.

Together with the already checked201tick all-outcome bound this is the
complete local encoder interface needed by the actual withdrawal loop.
That loop's prefix rows/heap progression, complete indexed withdrawal trie,
remaining header/main and uniform target-step theorem remain outstanding.

Validation: current-withdrawal-encoder-normal-v1.log PASS863jobs; permitted
printed axioms only. Index8700modules/17899facts; inventory8745/replacement
closure0/fixed files unchanged. Incremental policy65536entries/2485857622bytes
(entry cap full). Claim infinity; no global finite target K/full verifier
success. Usage45%weekly/0resetcredits. Final cleanup stays on the plan.

## Actual withdrawal-loop encoder entry, iteration price and output

The current withdrawal-loop model tracks only already filled array rows,
owned array/current heap and the retained decoded input. Every active real
row pointer supplies the actual current779 ABI and full input/heap entry.
The unchanged complete iteration now costs at most202body source ticks,
including the encoder caller, both scalar stores and counter increment,
on every outcome. No future successful store or row is supplied.

The same observed scoped encoder return derives the exact e pair, its
positive1..57 length, own64-byte allocation and checked persistent room,
next heap exactly64bytes later, unchanged older memory and complete retained
Data contract before the footer. A shared Data.of_heap_frame handles actual
heap advances while preserving all nonheap globals and decoded prefix bytes.
The public encoder normal contract explicitly retains its own checked room.

Validation: current-withdrawal-encoded-row-v1.log PASS2709jobs; permitted
printed axioms only. Index8700modules/17907facts; inventory8745/replacement
closure0/fixed files unchanged. Incremental policy65536entries/2485875811bytes
(entry cap full). Claim infinity; no global finite target K/full verifier
success. Usage45%weekly/0resetcredits. Next: actual footer stores/counter and
full loop invariant, initialized-array entry to withdrawal trie, remaining
header/main, target composition, dominant-slack review and cleanup.


## Complete actual withdrawal prefix and main reaches execution requests

Both original array stores and counter increment now execute with their exact
state and retain every older initialized row. Normal iterations derive the
next complete model; all repeated-loop outcomes cost≤203*(remaining rows),
uniformly68115432source ticks. A normal exit has the exact original count and
a completely initialized, owned nonempty slice array. The actual count/global-
allocation/i=0 prefix constructs that model from the same earlier header/data;
no future rows or allocation room are supplied.

The literal withdrawal-trie call instantiates the existing complete current
indexed-builder proof from that real array/latest heap/startup empty root and
owned wr buffer. It costs≤12357078900caller source ticks at count≤335544.
A true normal return forces the actual decoded withdrawal count zero and
retains its caller metadata and earlier memory outside wr. Complete withdrawal
work through this caller costs≤12425194334source ticks or reaches requests.

Composing with the earlier actual transaction trie gives the whole original
payload_header trace to encode_execution_requests:≤476207133311source ticks
or a real reached continuation. It has zero transactions/withdrawals, complete
Data, all31header cells/facts, owned buffers and actual h/pl/rh/bh/bl bindings.
No requests, hash, EVM or main success is assumed. The actual program is unchanged.

Validation: current-main-before-requests-v1.log PASS2709jobs; permitted printed
axioms only. Index8700modules/17934facts; inventory8745/replacement closure0/
fixed files unchanged. Incremental policy65536entries/2485933997bytes (entry
cap full). Claim infinity; no global finite target K/full verifier success.
Usage46%weekly/0resetcredits. Next: retain the actual decoded request image
through Data, requests encoder/hash/BAL suffix, remaining current main, formal
target-step composition, dominant-slack review and cleanup.

## Decoded execution requests survive the complete actual main prefix

Main's same real decoder/root return now derives the SI+32 request-record
pointer and full Requests.DecodedImage: all ten actual pointer/count cells,
validated five-list layout and arithmetic, copied input extent and owned
80-byte record before the original allocation boundary. This physical image
is now part of Data and is transported by every existing actual earlier-
memory frame, heap advance and caller restoration through both indexed tries.
No execution-request encoder/hash return is assumed.

Validation: current-main-request-image-v1.log PASS2709jobs, including all
actual main users of the strengthened Data contract. Printed axioms permitted
only. Index8700modules/17935facts; inventory8745/replacement closure0/fixed files
unchanged. Incremental policy65536entries/2485938423bytes (entry cap full).
Claim infinity; no global finite target K/full verifier success. Usage46%weekly/
0resetcredits. Next: retain actual SHA state/pad globals for the general SHA
hash caller, execution-request encoding/hash/BAL suffix and remaining main,
then formal target composition, dominant-slack review and cleanup.

## Actual SHA startup cells and request-encoder entry

The same first three startup calls now derive all four SHA/Keccak pointers
in one proof. Actual sha_st2701131776 and sha_pad2701131840 survive the later
initializers, decoder/root allocation, entire original request-SSZ graph,
header validator, databases, state initializer and both indexed tries.
Workspace/Core/Cursor and full verification Data retain these actual global
cells; all normal transports derive them from the same caller executions.
The source program, SHA instructions and allocated bytes are unchanged.

ExecutionRequests checks the literal current main request caller and original
function780 ABI, derives its real RQ pointer and callee entry from Data, and
uses the one decoded five-list byte budget to prove every cnt*sz is nonwrapping.
All copied list bytes lie in their actual owned input slices before the real
incoming heap. No later allocation room, encoder/hash normal return or main
success is supplied. The complete encoder loop and SHA body/caller proofs are
still next.

Cleanup: DataActions is folded into its DataGlobals transport module without
changing theorem names or behavior. Its sole importer is updated, and the
new ExecutionRequests module uses the freed package entry. Removed stale
bookkeeping for the retired startup theorem/module.

Validation: current-sha-workspace-v1.log PASS1847jobs and
current-main-sha-inputs-v4.log PASS2709jobs. Printed axioms permitted only.
Index8700modules/17945facts; inventory8745/replacement closure0/fixed files
unchanged. Claim infinity; no global finite target K/full verifier success.
Usage47%weekly/0resetcredits. Continue with actual request encoder/hash/BAL,
remaining main, formal target composition, dominant-slack review and cleanup.

## Current execution-request loop entry and real width/field prefix

The literal encoder780 setup now costs≤2source ticks on every outcome.
Its same actual reached alloc80/declare-n0/declare-i0 execution derives the
allocator's own checked room, exact post-state, preserved request image and
vacuous initial LoopModel. The model owns the descriptor array, keeps real
RQ/input/heap separation and only requires images for already emitted rows;
there are no preinitialized future rows or future allocation successes.

The actual indexed pointer/count loads are mapped/aligned and read the same
ten decoder cells. All four original width decisions execute to exactly
192/76/116/184/68 for types0..4, preserving the arbitrary original continuation.
The real signed guard matches the bounded cursor, and every genuinely
continuing complete iteration advances i exactly once, including through
its real allocation/copy scopes. Model transport keeps already emitted rows
through pure local/clock changes. These are entry/progress facts, not yet a
complete encoder loop cost/normal result.

Validation: current-requests-setup-v3.log PASS2709jobs; permitted printed axioms
only. Index8700modules/17965facts; fixed files unchanged/replacement closure0.
Claim infinity; no global finite target K/full verifier success. Usage48%weekly/
0resetcredits. Next: actual prepared iteration, guarded blob allocation/copy,
normal row/frame preservation and whole encoder, then requests SHA/BAL and
remaining main/target composition, dominant-slack review and cleanup.

## Current request blob and complete iteration source allowance

The same actual two field reads and four width decisions now reach their
specific prepared state while preserving the original iteration's complete
nonlocal observation and remaining branch. All real p/cnt/sz/i/n/rq/arr
bindings and prior emitted rows are derived/transported at that same state.

The literal nonempty branch's own alloc(cnt*sz+8) supplies checked natural
room, returned pointer, exact saved-caller post-state and mapped destination.
Its actual tag store executes to the real first byte. The original memcpy
uses the accepted input-list pointer and count product, with owned source
and fresh destination. Its descriptor stores/increment spend no source ticks.
The allocation/copy suffix costs≤bytes/8+10 on every outcome, including failed
capacity checks and short clocks; room is obtained only from that same normal
allocator return, never supplied for a future call.

This composes through the complete unchanged real iteration, including its
field/width declarations, nonempty decision and final counter increment:
≤(counts[i]*elementSize[i]).toNat/8+10source ticks, uniformly31456889 from the
one actual decoded byte budget. This is not yet a repeated-loop theorem:
normal row/image/heap-frame preservation must still construct the next model.
No request-hash return, main success or target-step bound is assumed.

Validation: current-requests-iteration-cost-v1.log PASS2709jobs, permitted
printed axioms only. Index8700modules/17981facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K/full
verifier success. Usage48%weekly/0resetcredits. Next: same actual iteration's
normal next model and whole encoder, requests SHA/BAL, remaining main and
formal target composition, dominant-slack review and final cleanup.
