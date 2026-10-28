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

Latest checked steps: unchanged decode_header208 costs≤195*inputLength+473
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
  reset means an account usage-limit reset. Latest:16%weekly,0resetcredits,
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
