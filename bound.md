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

## Current status — 2026-10-30

**No global finite target K yet.** Claim infinity; no full verification claimed.
Best overall effort estimate: **55%, plausible45–65%**, relative to current main.
Module counts are bookkeeping. The old10^14–10^18 numerical guess was speculation,
not a theorem or target ceiling.

The current startup/input/header/gas/two-database/state-init path is connected
through both actual payload-header indexed tries. The complete unchanged
withdrawal encoder costs≤201body source ticks; its real loop costs≤203 per
row. The actual run_attempt prefix through payload_header, both indexed tries,
request encoding/hashing, BAL/header hashing and the version check either stops
or reaches the original
header-validation caller within479872713926source ticks, retaining all decoded
inputs/header fields and the actual restored heap. The request array/count≤5 and every helper entry are derived
from that same execution. Any reached continuation has zero actual transactions
and withdrawals, derived from the real trie executions.

These are all-outcome source-clock allowances, not formal target-step bounds.
Actual SHA state/pad globals now survive startup and this complete main prefix.
The request encoder receives the real five-list image, with nonwrapping sizes
and owned input slices before its incoming heap. Each actual iteration costs
≤(its encoded bytes)/8+10source ticks (uniformly31456889). Actual normal
iterations construct the next complete model; the whole original encoder
costs≤157284452body source ticks on every outcome. Its actual normal return
supplies the real count≤5, owned rows, checked heap and complete earlier-memory
frame. The actual main caller connection is checked. General software SHA now has a
complete all-outcome body source allowance2*(bytes/64)+268, plus1caller tick.
Its complete caller memory frame is checked. Request hashing and the full physical
header return are connected; the remaining main continuation,
uniform target composition, dominant-slack review and final cleanup remain open.

The complete unchanged Taylor body now costs at most 449602 source ticks;
its original blob-price caller costs 449604, and calculate_excess_blob_gas
costs 449690 body / 449691 caller ticks. Actual returns preserve all source
metadata and memory outside the fixed division workspace. The restored caller
can retain its complete decoded main-input record from the same execution.
The unchanged base-fee helper now costs at most 737 body / 738 caller source
ticks, including its actual zero-divisor return path. Its complete normal-return workspace frame and original ABI/caller are now
checked too. The actual header-validation prefix through the nonce comparison
is now bounded by 450464 source ticks, with its original header bindings and
outside-workspace memory retained. The empty-ommer hash/check adds at most
823 ticks, giving 451287 through the actual parent-header hash entry. Both
actual fee and temporary/hash memory frames now reach that entry. Parent
hashing, the restored whole header caller and main continuation remain open.

The unchanged memcpy now also has a checked arbitrary-length fallback:
43314052475 body / 43314052476 caller source ticks in the actual ordinary
memory domain, including wrapping length guards. Existing sharper known-length
bounds remain available. Actual normal returns now derive the finite
requested-length bound and complete runtime/earlier-memory frame. The
parent-header byte writer now has checked arbitrary-pointer/length body and
caller costs (43314052495 / 43314052496 ticks), with smaller known-length
variants. Actual returns now derive their positive encoded length, full metadata,
assigned result and earlier-memory frame without input ownership. The
encoder must derive its output-cursor conditions; encoding/hashing remain open. This is not a whole-program target K.

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
  reset means an account usage-limit reset. Latest:40%weekly,0resetcredits,
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

## Current normal request copy/descriptor state and earlier-memory frame

Actual normal per-list tag/copy/descriptor execution now derives memcpy's own
required clock and its exact complete caller state. The same observed normal
return supplies the new descriptor state and n++ value. Its two row words are
proved just written from the actual blob pointer and original cnt*sz+1 word;
no previous descriptor contents or future row are supplied.

The original p/cnt/sz lexical restorations now retain every other actual
post-iteration local at the same prepared continuation. The generic normal
suffix keeps full runtime/global metadata and every memory cell before its
current descriptor row. This frame includes earlier rows and all earlier
RQ/input cells: both the tag and the unaligned copy at blob+1 stay inside
the same actual aligned fresh allocation. The width/copy cost proof reuses
the shared literal tag execution helper.

Validation: current-requests-normal-frame-v2.log PASS2709jobs, permitted
printed axioms only. Index8700modules/17992facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K/full
verifier success. Usage48%weekly/0resetcredits. Next: attach the suffix to its
same normal allocator and construct the real next LoopModel (including empty
lists), repeated-loop/encoder normal result, requests SHA/BAL and remaining
main/target composition, dominant-slack review and final cleanup.

## Complete original execution-request encoder source-clock bound

The same actual normal guarded blob call now derives its own natural room,
exact copied/descriptor state and original scoped restoration. Empty-list
skips and newly emitted rows each construct the next real complete LoopModel.
The nonempty case adds only its own just-written row; prior rows and all ten
RQ fields remain intact, and the new bounded/aligned heap comes from that
same allocation. The actual final i++ and all p/cnt/sz/blob scopes retain
normal next-model progress, nonheap globals and every memory cell before
the original descriptor array. No future row, call or funding is supplied.

The real loop body cannot return/break/continue to its caller. Its actual
normal transition decreases rank5-i; failed or short-clock bodies need no
future model. The complete original repeated loop therefore costs at most
31456890*(5-i), uniformly157284450source ticks. Its actual array allocation/
zero-counter setup costs≤2, and its tuple return spends0. Complete unchanged
encode_execution_requests780 costs≤157284452body source ticks on every
outcome from the real main-derived Entry, including allocator failures and
all clock budgets. Straight-line target work is still not included.

Validation: current-requests-body-cost-v2.log PASS2709jobs, permitted printed
axioms only. Index8700modules/18011facts; inventory8745/replacement closure0/
fixed files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage49%weekly/0resetcredits. Next: complete normal loop exit/returned
array and actual main caller frame, requests SHA/BAL and remaining main, formal
target composition, dominant-slack review and final cleanup.

## Complete actual encoder normal return and physical rows for hashing

The real normal loop exit has visited all five types, has the actual emitted
count≤5 and initialized row prefix, and retains monotone checked heap,
nonheap globals and all memory before its original array. The original tuple
return is read from those actual arr/n bindings. Real setup/loop/return traces
now derive the full encode_execution_requests normal result: returned(array,
count), physical owned rows and bounded/aligned current heap, with every older
caller memory cell and other global retained through the original scopes.

Returned exposes this physical result independently of retired loop locals,
and transports it through the actual caller restoration. Its blobs have real
mapped extents and lengths1..251655057, entirely before the returned heap.
No future hash or main success is supplied. The complete encoder's all-outcome
source allowance remains157284452body ticks; target steps remain open.

Validation: current-requests-body-normal-v1.log PASS2709jobs; permitted printed
axioms only. Index8700modules/18016facts; inventory8745/replacement closure0/
fixed files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage49%weekly/0resetcredits. Next: retain the actual post-header heap
frontier through the withdrawal/root prefix (needed to frame header buffers
past requests), actual main encoder caller/requests SHA/BAL, remaining main,
formal target composition, dominant-slack review and cleanup.

## Actual main request encoder caller and full prefix to request hashing

BeforeRequests now retains the actual heap past headerFrontier+16. This is
derived from the same completed withdrawal-array allocation and normally
restored indexed-root caller, without a new global hypothesis. It establishes
that encoder allocations follow every already allocated header buffer.

The same literal scoped encode_execution_requests invocation supplies its
actual returned array, count≤5 and physical rows at the real reqs binding.
The complete Data, all31header fields, RH/BH bindings, original bl/zero-TX/WD
facts and stronger header/heap frontier survive that same body return and
caller restoration. No later hash or main success is supplied. The actual
caller costs≤157284453source ticks or reaches its unchanged continuation.

Composing it with the prior two-tries/header trace gives the full original
payload_header prefix to compute_requests_hash:≤476364417764source ticks or
an actual reached BeforeHash continuation. Its real request inputs and output
buffer, decoded inputs and initialized SHA/Keccak pointers are retained.
This is a source-clock prefix theorem, not the global formal target bound.

Validation: current-main-before-requests-hash-v1.log PASS2709jobs, permitted
printed axioms only. Index8700modules/18021facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K/full
verifier success. Usage49%weekly/0resetcredits. Next: actual general SHA/block/
finish contracts, request-hash loop/caller and BAL Keccak suffix, remaining
main, formal target composition, dominant-slack review and final cleanup.

## Current general software SHA helper checks

The actual SHA84/85/86/87 declarations and code indices are now checked.
The original expanded state initializer and compression block are kernel-
checked straight bodies:0body source-call/loop ticks on every outcome, and
every global retained. Their substantial straight-line target work is still
an open static-cost obligation.

A shared scalar-word-store frame reuses the existing checked straight-prefix
composition rules. Successful const/op/shift values flatten to at most one
word, failed stores keep memory unchanged, and the literal SHA state/body
syntax is checked against its stable stp and64-byte region. Every actual
initializer/block outcome therefore preserves memory outside that state,
without successful-read, digest-value or future-body-return premises.

Original sha256_finish86's real8-iteration st_be32 loop costs≤16body source
ticks on every outcome, including errors and exhausted clocks. Each original
st_be32 has0body ticks and a single caller tick; normal bodies derive i++.
The full general SHA loop/padding and complete memory/caller frame remain next.

Validation: current-general-sha-finish-cost-v2.log PASS2710jobs; permitted
printed axioms only. Index8700modules/18042facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K/full
verifier success. Usage50%weekly/0resetcredits. Next: share the existing stride
rule across actual n/len locals, SHA block loop/padding/output frames, actual
request-hash and BAL/main continuation, formal target composition, dominant-
slack review and final cleanup.


## Current complete general SHA source-clock allowance

CounterFlow.NamedStride now shares the checked stride transition/cost/normal
argument across the actual length-local name. Existing n-based public APIs
remain specializations; current Keccak and all selected clients rebuild.
The real SHA len-based64-byte block loop costs≤2*(length/64)source ticks on
every outcome and derives its own normal exit remainder<64.

The literal general SHA shape, padding, length writer, one/two final blocks
and eight-word digest loop compose to≤2*(length/64)+268body source ticks,
plus1caller tick. The current st_be64's aligned bswap and two-BE32 fallback
are both included (≤3body ticks); no straight-body assumption is imposed.
The actual three-word p/len/out ABI and known-size dynamic caller cover
failed or ill-typed other argument expressions as well. No successful pointer
mapping, future read, completed hash or cryptographic result is assumed.
Expanded compression/straight-line target work remains separate.

Validation: current-general-sha-block-loop-v1.log PASS2710jobs and
current-general-sha-body-cost-v4.log PASS2710jobs, permitted printed axioms
only. Index8700modules/18065facts; inventory8745/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage50%weekly/0resetcredits. Next: complete actual SHA workspace/
output/caller memory frames, request-hash loop and BAL/main continuation,
formal target composition, dominant-slack review and final cleanup.


## Current SHA global, digest and block-loop memory frames

All actual general SHA outcomes retain every global, including the real
state/pad pointers and heap. The original BE32 writer frame is checked from
current syntax and its same-call first-argument ABI; actual second-argument
read/shape success comes from the real normal call. The eight-iteration
finish loop and complete digest body therefore preserve every memory word
outside its32output bytes, without supplied digest contents or later success.

Actual state-init/compression/digest caller frames retain the same protected
word through their ordinary call restoration. The real block loop only
writes its64-byte state. Its memory invariant only needs the actual state
global; counter/length progress is separately checked for the source bound.
Current allocated workspace Environment/Frame helpers now retain real globals,
domain, caller locals and protected memory through actual zero/copy/byte-store/
compression/digest calls. Padding placement and complete SHA/main caller
composition remain open. The generic constant-loop memory proof was ported
to the currently available contradiction tactic; no hypothesis was added.

Validation: current-general-sha-helper-memory-v6.log PASS2711jobs, permitted
printed axioms only. Index8700modules/18095facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K/full
verifier success. Usage50%weekly/0resetcredits. Next: current optimized64-bit
length-writer memory frame, full SHA padding/body/caller frame, request-hash
and BAL/main continuation, formal target composition, dominant-slack review
and final cleanup.


## Current64-bit SHA length-writer memory frame

The actual optimized st_be64 shape is now checked directly. Its bswap64
callee only changes locals; the real scoped return supplies a scalar w for
the single-word store. Both the actual aligned fast branch and the two-BE32
fallback preserve every memory word outside the eight output bytes. The same
normal ordinary caller retains this frame through its actual two-word ABI.
No mapped output, successful future writer, byte-swap value or completed SHA
is an entry premise. This avoids importing retired arithmetic/EVM proof roots.

Validation: current-general-sha-be64-memory-v3.log PASS2712jobs, permitted
printed axioms only. Index8700modules/18101facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K/full
verifier success. Usage51%weekly/0resetcredits. Next: complete actual SHA
padding/body/caller frames, request-hash and BAL/main continuation, formal
target composition, dominant-slack review and final cleanup.


## Complete current general SHA memory/body/caller contract

The original padding selection is derived from its actual normal branch:
total is64 or128. Its length writer targets the corresponding final8-byte
subrange of the real128-byte pad. Actual zero/copy/marker/length/final-block/
digest executions preserve every word outside state64, pad128 and output32.
The real loop exit supplies remainder<64 and the actual owned input suffix;
all length/pointer/output cells are carried through the same reached scopes.

The complete unchanged sha256 body now retains this memory frame through
its actual initializer, normal block loop, remainder declaration and every
padding/output phase. The actual three-word p/len/out caller lifts that same
frame through its ordinary return. No digest value, future read/store/hash
success or extra allocation funding is assumed. Source cost remains
≤2*(bytes/64)+268body ticks/+1caller; target static/straight-line cost remains
separate. Main request-hash loop/caller composition is still open.

Validation: current-general-sha-padding-frames-v2.log PASS2712jobs and
current-general-sha-body-memory-v1.log PASS2712jobs, permitted printed axioms
only. Index8700modules/18113facts; inventory8745/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage51%weekly/0resetcredits. Next: separate completed SHA into its
own helper module while consolidating related loop utilities to retain the
package entry cap; actual request-hash and BAL/main continuation, formal
target composition, dominant-slack review and final cleanup.


## Completed SHA/helper module cleanup

The checked general SHA contracts now live in CurrentVerify/GeneralSha.lean,
with explicit minimal proof dependencies and one namespace/axiom-print block.
ExecutionRequests.lean imports this module and retains the request encoder/
main-prefix proofs. Moved theorem names and proof text match the previous
checked checkpoint; no hypothesis or executable changed.

CounterStrideLoop's named-stride rules/public n-specializations were merged
into the related existing CounterStrideCost module, and all seven import
sites were repointed. Deleting the old module offsets the new SHA module:
the package remains exactly65536entries. The proof index now drops deleted
module paths before recording successful builds, so moves cannot leave a
nonexistent module recorded as current checked source.

Validation: standalone current-general-sha-module-cleanup-v2.log PASS819jobs
and current-sha-module-client-cleanup-v1.log PASS2712jobs. Permitted printed
axioms only. Index8700modules/18113facts (one moved module added/one removed);
inventory8745/replacement closure0/fixed files unchanged. Claim infinity; no
global finite target K/full verifier success. Usage51%weekly/0resetcredits.
Next: actual compute_requests_hash loop/caller and BAL/main continuation,
formal target composition, dominant-slack review and final cleanup.


## Actual request-hash row loop and input preservation

The literal compute_requests_hash781 body, main caller and arr/n/out ABI are
checked. Data.general_sha derives the real startup state64/pad128 workspace
from the already retained main input contract. A physical Image exposes the
encoder's real owned rows independently of the temporary allocator's current
heap pointer; its actual len load prices each SHA iteration≤7864489source
ticks on every outcome, with no later successful hash/read premise.

A real normally completed row SHA preserves every word at or above2701131968
and below the original heap; this includes all remaining rows, older input
and header data. Its output address geometry follows from the actual counter
and bounded/aligned old heap. The real i++ constructs the next complete loop
model. Actual signed test/progress gives≤39322450source ticks for all five
rows including loop ticks. A genuine normal exit derives index=count and the
same physical image/prefix. Setup allocation, final concatenated digest,
release and main caller composition remain open.

Validation: current-request-hash-syntax-v2.log PASS2712jobs,
current-request-hash-model-v3.log PASS2712jobs, current-request-hash-loop-cost-v1.log
PASS2712jobs and current-request-hash-loop-normal-v1.log PASS2712jobs. Permitted
printed axioms only. Index8700modules/18134facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K/full
verifier success. Usage51%weekly/0resetcredits. Next: derive this loop entry
from its actual mark/temporary allocation, final digest/release, main request-
hash/BAL continuation, formal target composition, dominant-slack review and
final cleanup.


## Complete current request-hash body and main-entry source bound

The actual heap_mark return derives its saved old pointer and full reached
state. The actual temporary alloc derives its own room for32*count+8bytes
and original cat pointer; setup preserves every row and all retained SHA
metadata. It therefore constructs the initial index0 loop model without
assuming any later hash return or allocation funding. Setup costs≤3source
ticks including the allocator's own failure trap.

The final concatenated digest reads actual n*32≤160bytes, then releases its
mark and returns, at≤274source ticks on every outcome. Combined with the
real row loop, unchanged compute_requests_hash781 costs≤39322727body source
ticks. The real main reqs tuple/owned rows/header RH pointer derive its same
arr/n/out callee ABI and full Entry; its caller costs≤39322728ticks.
The completed-call memory/heap frame and continued main/BAL trace remain open.

Validation: current-request-hash-setup-cost-v1.log PASS2712jobs and
current-request-hash-body-cost-v2.log PASS2712jobs, permitted printed axioms
only. Index8700modules/18148facts; inventory8745/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage52%weekly/0resetcredits. Next: actual request-hash normal whole-
body/caller frame, BAL/main continuation, formal target composition,
dominant-slack review and final cleanup.


## Complete actual main request hashing and prefix to BAL

The normally completed helper derives its real saved mark, own temporary
allocation room, normal row-loop exit and final concatenated SHA, then
restores its actual old heap through heap_release and every original scope.
It returns0, retains every nonheap global and preserves earlier memory at/
above2701131968 outside its output32. The ordinary main caller lifts those
same-run heap and memory facts through its actual checked arr/n/out ABI.

Main's RH output is separated from all older decoded input and31header cells.
The complete Data, real heap/frontier, header fields/buffers, bl/h/pl/rh/bh
bindings and zero-TX/WD facts therefore survive at the original BAL hash.
A cell-based header transport avoids demanding preservation of SHA's own
lower workspace. The full original payload_header prefix through request
hashing stops or reaches this actual BeforeBalance continuation within
476403740492source ticks. BAL and complete main/target composition remain open.

Validation: current-request-hash-final-normal-v2.log PASS2713jobs and
current-main-before-balance-v1.log PASS2713jobs, permitted printed axioms
only. Index8700modules/18160facts; inventory8745/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage52%weekly/0resetcredits. Next: actual BAL Keccak/complete header
return, remaining run_attempt/main, formal target composition, dominant-slack
review and final cleanup.


## Complete unchanged payload_header source-clock allowance

The actual final decoder offset supplies BAL pointer/length cells, a real
owned input extent and length≤251655056. Its current Keccak caller therefore
costs≤81418466source ticks on every outcome; no successful future input read
or digest is supplied. The original final return adds0source ticks.

The full payload_header788 body now has the checked all-outcome source
allowance476485158958, composed from its actual main-derived inputs and
transaction-record scan through both tries, requests and final BAL call.
This is still source clock, not the global formal target bound.

The remaining normal-return connection needs state observations through
outer lexical scopes, in addition to the clock equality carried by current
cost traces. Next, strengthen those trace conclusions with a ScopeFrame
(clock plus LocalEffects metadata), finish the actual BAL/header normal
return and connect the remaining run_attempt/main continuation. No entry
hypothesis or executable change is required for this stronger conclusion.

Validation: current-payload-header-body-cost-v1.log PASS2713jobs, permitted
printed axioms only. Index8700modules/18166facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K/full
verifier success. Usage52%weekly/0resetcredits. Remaining: state-carrying header
return/main, formal target composition, dominant-slack review and final cleanup.


## Complete state-carrying actual header return

CallPrefix.ScopeFrame retains the actual final clock and all fields except
locals. Its new priced_frame_trace is checked from the same full scope
observation; the original clock-only API remains available. The current
header/length/size/two-tries/withdrawal/requests traces now propagate this
stronger conclusion. No entry hypothesis, allowance or executable changed.

The real final BAL Keccak preserves all older decoded/header cells outside
its actual32-byte output and lower workspace. Its original final Return
supplies the actual header word. The complete payload_header normal-return
theorem now carries its same physical31-field header/Data/heap state through
all enclosing lexical scopes, without claiming callee locals survive Return.
This is the state needed by main's actual hdr caller. All-outcome body source
cost remains476485158958. Formal target-step composition is still open.

Validation: current-scope-frame-trace-v1.log PASS123jobs,
current-header-scope-frames-v1.log PASS2713jobs and current-payload-header-normal-v1.log
PASS2713jobs. Permitted printed axioms only. Index8700modules/18173facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity; no
global finite target K/full verifier success. Usage53%weekly/0resetcredits.
Next: actual run_attempt hdr call, header hash/comparison/version checks and
remaining main continuation, formal target composition, dominant-slack review
and final cleanup.


## Actual main caller receives the completed payload header

The original run_attempt hdr call now derives its real returned word from
payload_header's actual normal execution. Its actual caller restoration retains
SI/PL, the complete decoded input, all31header-field facts, allocated buffers,
bounded aligned heap and the derived zero transaction/withdrawal counts.
No later hash result, success, funding or extra entry hypothesis is assumed.

The complete original prefix through that call either stops or reaches its
unchanged header-validation caller within479872713926source ticks. Header
caller alone costs476485158959. These remain source-clock allowances; global
uniform target-step composition remains open. Joining the previously separate
proof paths exposed two identically named node-constructor shape lemmas;
the cost-only duplicate is now private, without changing either proof or ABI.

Validation: current-main-header-caller-v5.log PASS3090jobs, permitted printed
axioms only. Index8700modules/18180facts; inventory8745/replacement closure0/
fixed files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage53%weekly/0resetcredits. Next: actual header hash/comparison/
version checks and remaining main, formal target composition, dominant-slack
review and final cleanup.


## Complete current header_hash body and ordinary caller

The original header_hash211 now costs≤2303body/2304caller source ticks on
every outcome. The actual encoder return supplies its real1..916-byte length;
software Keccak costs≤954caller ticks for this same output. Its own mark,
encoder allocation/temporary failures, release and scalar return are included.
Normal execution restores its own saved heap and all older memory outside
its real32-byte output and fixed lower Keccak workspaces, while preserving
all nonheap globals and the caller's actual locals. The signature/ABI comes
from the unchanged two-word h/out code entry. No digest value, future read,
completed hash or allocation room is supplied as an entry premise.

Validation: current-main-header-hash-cost-v1.log PASS3090jobs,
current-main-header-hash-tail-normal-v1.log PASS3090jobs,
current-main-header-hash-normal-v1.log PASS3090jobs and
current-main-header-hash-call-v2.log PASS3090jobs, permitted printed axioms
only. Index8700modules/18190facts; inventory8745/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage54%weekly/0resetcredits. Next: actual main bh allocation/hash
continuation, comparison/version checks and later main, formal target
composition, dominant-slack review and final cleanup.


## Actual main allocation/hash continuation

The original bh allocation and header_hash call now have a complete actual
main trace. The allocation's own normal return supplies its32-byte room,
output arena and bounded aligned advanced heap; no future funding is assumed.
Header encoder geometry follows from that real cursor and earlier header.
Hashing/releasing preserves all31header facts and complete earlier decoded
inputs, with real caller SI/PL/hdr and derived zero TX/WD counts retained.

This prefix costs≤2306source ticks. The complete run_attempt prefix through
payload_header and header hashing either stops or reaches the original
header-validation caller within479872713926source ticks. This is not a
uniform target-step K. Main comparison/version/header validation/execution,
formal target composition, dominant-slack review and final cleanup remain open.

Validation: current-main-header-hash-prefix-v2.log PASS3090jobs and
current-main-header-hash-complete-v1.log PASS3090jobs, permitted printed
axioms only. Index8700modules/18196facts; inventory8745/replacement closure0/
fixed files unchanged. Claim infinity; no full verifier success.
Usage54%weekly/0resetcredits. No executable or entry hypothesis changed.


## Actual main header comparison and version-check entry

The real block-hash memeq call, BlockErr5 guard and following skip now have
an all-outcome source allowance129 using the existing comparison caller
contract. Its physical read-only frame and actual lexical bindings retain
the complete decoded input, header, heap and derived zero TX/WD counts.
The reusable AfterHeader.of_frame contract now handles later read-only checks.

The complete unchanged run_attempt prefix either stops or reaches its actual
is_valid_versioned_hashes caller within479872713925source ticks. No equality
result, future guard success or external hypothesis is supplied. The remaining
version/header validation/execution and formal uniform target composition
remain open, followed by dominant-slack review and cleanup.

Validation: current-main-header-compare-v2.log PASS3090jobs and
current-main-header-compare-complete-v1.log PASS3090jobs, permitted printed
axioms only. Index8700modules/18204facts; inventory8745/replacement closure0/
fixed files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage54%weekly/0resetcredits.


## Complete reached zero-transaction version check and main caller

The original is_valid_versioned_hashes792 now has an all-outcome zero-source-
clock/full-nonlocal-state observation at the actual zero transaction count
already derived from the original tries. Its real SI/payload/transaction
loads come from main's retained decoded image. Later vh/nvh setup reads may
fail or return any checked word; no successful future read is assumed. The
literal signed loop test is false at i=ntx=0, so transaction decoding/blob
comparison calls cannot run. The original final return/guard is retained.
A generic same-execution declaration frame handles failed reads, shape checks
and lexical restoration without changing an entry hypothesis.

The actual main vvh call and BlockErr6 guard cost≤1caller source tick and
retain the full header/input model. Whole run_attempt either stops or reaches
the literal validate_header caller within479872713926source ticks. Target
straight-line work remains separate; no global finite target K exists yet.

Validation: current-versioned-hashes-zero-tail-v6.log PASS3090jobs,
current-versioned-hashes-zero-body-v1.log PASS3090jobs and
current-versioned-hashes-complete-v1.log PASS3090jobs, permitted printed
axioms only. Index8700modules/18226facts; inventory8745/replacement closure0/
fixed files unchanged. Claim infinity; no full verifier success.
Usage54%weekly/0resetcredits. Next: current validate_header and its actual
parent-header state. Earlier validate_headers normal contracts retain physical
row/header data, but current main Data traces only carry the earlier decoded
input, so inspect and retain the real parent contract through the intervening
calls. Remaining execution/wrappers/main, uniform target composition,
dominant-slack review and final cleanup remain open.


## Geometric Taylor arithmetic and standalone current arithmetic values

The checked natural recurrence has a finite positive-prefix limit: fewer
than1280continuing steps for256-bit terms. A numerator≥512denominator
forces doubling before index257; the other branch forces halving from
index1024. Generic doubling/halving/quotient lemmas establish these claims
without assuming an infinite path or a successful future helper. This is
not yet a bound for the actual taylor_exponential body: its real multiply,
divide, overflow and loop-guard execution still must supply that recurrence.

The44-entry arithmetic catalogue is now checked directly against the current
Software AST, with fresh literal positions, independent of the retired
whole-EVM environment. The existing Mul64 value and U256 zero/equality
proofs now import only their needed arithmetic/tuple/return dependencies.
Their original proof text and APIs are retained; each has an actual current
code-entry theorem. Natural carry/low/high-half identities are checked. The
real four-limb number is below2^256, and the actual zero-test returns0 exactly
when that number is positive. Full multiply/divide numerical contracts remain
open. No executable or challenge hypothesis was changed.

Validation: current-taylor-geometric-arithmetic-v2.log PASS204jobs,
current-main-geometric-compatibility-v1.log PASS3090jobs and
current-arithmetic-value-imports-v2.log PASS735jobs, permitted printed axioms
only. Index8700modules/18250facts; inventory8745/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage55%weekly/0resetcredits. Remaining: actual Taylor arithmetic/
progress, parent-header field-size facts and current header validation,
execution/wrappers/main, uniform target composition, dominant-slack review
and final cleanup. Earlier header normal contracts retain allocation/input
geometry but do not yet expose all materialized parent field-size facts.


## Actual current wide-division zero-divisor branch and wrapper

The literal u256_divmod63 zero-divisor guard returns the real eight-zero
quotient/remainder tuple at every source clock, before reading its numerator,
workspace or numerical division helpers. It spends0body source ticks and
retains every nonlocal field. The actual u256_div64 wrapper has a checked
current signature and two-quadruple callee entry; its zero-divisor path costs
≤1body source tick on every outcome, including clock0timeout. Every actual
normal wrapper return supplies the real four-zero quotient tuple, with the
same full nonlocal frame. No general division-correctness oracle is used.

A reusable two-quadruple actual ABI now serves both division and the existing
U256 equality call, replacing that equality helper's duplicate lookup proof
without changing its public statement. No executable or challenge hypothesis
changed. This is a concrete arithmetic stopping case, not yet a whole Taylor
or global finite target-step bound. General multiply/divide progress and the
1280natural recurrence connection remain open.

Validation: current-wide-division-zero-v2.log PASS733jobs and
current-wide-division-wrapper-zero-v3.log PASS738jobs, permitted printed
axioms only. Index8700modules/18261facts; inventory8745/replacement closure0/
fixed files unchanged. Claim infinity; no global finite target K/full verifier
success. Usage56%weekly/0resetcredits.


## Exact numerical result of the current scalar multiplication helper

The actual mul64x64 execution now supplies two returned words whose natural
value low+2^64*high is exactly the input product. The proof checks all four
32-bit partial products, the middle carry, low-word shift and final high-word
addition; the latter is proved not to overflow. Reusable half-word and shifted
carry facts are included. The execution summary retains the same real return
and full nonlocal frame, with no added entry assumption or executable change.
This is an arithmetic bridge for the current wide multiply/Taylor proof, not
a complete Taylor or global target-step bound.

Validation: current-mul64-natural-product-v4.log PASS861jobs; all printed
axioms permitted. Index8700modules/18268facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K or
full verifier success. Overall estimate remains50%, plausible40–60%.


## Current wide multiplication fast branch and actual word conversion

The original u256_mul fast branch now has an exact functional contract for
two one-word four-limb inputs. Its real mul64x64 call returns the exact
128-bit product in the low two output limbs, with the upper two limbs zero.
The checked caller resumption spends exactly one source tick and preserves
all nonlocal state. Its all-outcome allowance is1body source tick, including
clock0. Every actual normal return derives clock funding and the concrete
result, without assuming a future successful helper. The original
u256_from_word conversion and current signatures are checked as well. These
facts cover the actual Taylor initial product and index/denominator products;
their Taylor caller connection, full-width product and numerical division
contracts remain open. The actual program and challenge assumptions are fixed.

Validation: current-wide-multiply-word-v3.log PASS868jobs; all printed axioms
permitted. Index8700modules/18280facts; inventory8745/replacement closure0/
fixed files unchanged. Claim infinity; no global finite target K or full
verifier success. Overall estimate remains50%, plausible40–60%. Usage57%
weekly/0resetcredits. Remaining parent-header validation/execution/wrappers/
main, uniform target composition, dominant-slack review and cleanup remain
part of the same active goal.


## Actual full-multiply scalar accumulation and exact overflow arithmetic

The unchanged u256_mul_full straight-line tail now has a checked execution
contract for the scalar-right-operand case needed by Taylor. After its real
sixteen partial products have their specified values, all111local updates
return the concrete eight-limb result and preserve every nonlocal field and
clock. The twelve products with zero right limbs are zero; six nonzero
carry operations remain. The proof follows the literal original tail.

The corresponding natural identity is checked: the four low limbs plus
2^256 times the fifth limb plus2^320 times the sixth limb equal the full
256-by64-bit input product. The high-limb OR test is zero exactly when this
product is below2^256; passing it leaves the exact mathematical product in
the four low limbs. This supplies the numerical meaning needed by the real
Taylor overflow guard. The sixteen-call prefix must still derive the tail's
partial-product bindings from that same actual run; no whole-helper or
Taylor recurrence connection is claimed yet. Numerical division remains open.

Validation: current-wide-multiply-scalar-tail-v4.log PASS986jobs; all printed
axioms permitted. Index8700modules/18284facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K or
full verifier success. Overall estimate remains50%, plausible40–60%. Usage57%
weekly/0resetcredits. No executable or challenge hypothesis changed.


## Actual sixteen-product full multiplication and caller resumption

The previous tail assumptions are now derived from the same actual original
u256_mul_full execution with a scalar right operand. The real sixteen
mul64x64 calls supply all sixteen physical local bindings, including the
twelve zero products. Every actual normal full-body return derives at least
16incoming source ticks, returns the exact checked eight-limb scalarValue,
and retains the complete nonlocal frame at exactly16ticks spent. No future
helper success, result or funding is assumed. The genuine current two-quad
ABI and actual callee return now resume the caller with this value and the
canonical full caller state after17source ticks, deriving that funding too.
Together with scalar_product/scalar_overflow, this closes the numerical
multiplication/overflow bridge for the original Taylor scalar numerator.
The Taylor step connection and numerical division still remain open.

The long generated accumulation proof now suppresses repetitive unused-simp
and sequence-focus lints locally; its checked execution statements and
proofs are unchanged. Existing UDivMod.ArithmeticBits/ArithmeticInvariant
provide checked restoring-division conservation lemmas to inspect for reuse
by actual div64by32 (32iterations, lo/d names and incoming high remainder).
The wider digits/Knuth numerical bridge and its physical workspace still
need proof; no division correctness is inferred from this reuse opportunity.

Validation: current-wide-multiply-scalar-normal-v2.log PASS986jobs; all printed
axioms permitted. Index8700modules/18290facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K or
full verifier success. Overall estimate remains50%, plausible40–60%. Latest
account read29%weekly/0resetcredits, ordinary usage allowed (earlier read57%).
No executable or challenge hypothesis changed. Remaining current parent-header
validation/execution/wrappers/main, uniform target composition, dominant-slack
review and final cleanup stay in the active goal.


## Complete actual div64by32 arithmetic, clocks and caller ABI

The restoring-division invariant now carries an explicit natural dividend,
so the real32-bit helper can start with an incoming high remainder while
consuming only32low bits. The existing scalar division step/finish proofs
use this shared invariant through wrappers with their original statements.
Its actual seed is high*2^32+low; checked transitions conserve that value
and retain remainder<divisor and quotient-bit alignment.

The literal current div64by32(57) has complete step/loop/setup execution
contracts and an all-outcome32body-source-tick allowance at real typed
entries, including short-clock outcomes. Actual normal execution derives
its own32ticks. For real digit inputs (low<2^32, divisor<2^32,
incoming high<divisor), its actual returned q/r words are exactly natural
division/remainder of high*2^32+low, with q<2^32 and r<divisor. The
true three-scalar ABI prices calls at33source ticks plus the continuation.
Every actual valid normal child return derives33caller ticks and resumes
the genuine caller with the concrete q/r pair and canonical full state.
The helper changes no nonlocal field; no future success/funding is assumed.

Validation: current-div32-seeded-arithmetic-v1.log PASS928jobs,
current-div32-loop-v1.log PASS968jobs, current-div32-body-v2.log PASS972jobs
and current-div32-complete-v3.log PASS975jobs. Final successful graph covers
both changed modules and existing unsigned-division APIs; printed axioms
permitted. Index8700modules/18305facts; inventory8745/replacement closure0/
fixed files unchanged. Claim infinity; no global finite target K or full
verifier success. Overall estimate remains50%, plausible40–60%. Usage29%
weekly/0resetcredits, ordinary usage allowed. No executable or challenge
hypothesis changed.

Next: actual digit-array/normalization and divmnu numerical contracts, then
the actual wide division/Taylor recurrence. The qhat correction guard is
rhat<2^32; with normalized vtop≥2^31, every continuing correction increases
rhat by vtop without64-bit overflow, so at most2corrections are possible.
This is an inspected proof plan, not a proved current loop bound. The actual
u256_ws640-byte allocation/global must also be retained from startup through
the current main prefix; current main Data does not yet expose that model.
Parent-header validation/execution/wrappers/main, uniform target composition,
dominant-slack review and final cleanup remain in the same active goal.


## Actual nlz32 normalization, returned count and caller frame

The five literal top-bit masks now have exact natural threshold facts on
32-bit inputs. Each real conditional shift raises the known lower bound,
stays below2^32 and conserves original*2^count. The original final one-bit
count update is included (its code does not shift x again). Complete current
nlz32(56) execution on a positive32-bit input returns a count≤31 such that
2^31≤original*2^count<2^32, with every nonlocal field and clock unchanged.
Its whole body has an all-outcome0source-clock allowance, independent of
input validity; the real call costs1tick plus its continuation. Current
unary ABI/caller execution and actual child-return resumption are checked.
The child-only resumption does not infer positive caller funding for a
zero-cost child; that comes from the actual scoped parent execution.

The actual normalization expression combining the shifted leading digit,
carry from its predecessor, and32-bit mask retains the leading half-bit:
its natural value is in[2^31,2^32). This holds for every predecessor word.
These facts establish the numerical normalization ingredient, not yet the
physical normalized-array image or a complete divmnu bound/correctness proof.
The leading nonzero digit, workspace ownership and normal-store history
still must come from the genuine surrounding digit-array execution.

Validation: current-nlz32-mask-v1.log PASS975jobs,
current-nlz32-finish-v1.log PASS975jobs and current-nlz32-complete-v3.log
PASS976jobs; printed axioms permitted. Index8700modules/18317facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Overall estimate
remains50%, plausible40–60%. Usage29%weekly/0resetcredits, ordinary usage
allowed. No executable or challenge hypothesis changed.

Next: literal quotient correction. A useful current-loop rank is0when
again≠1, otherwise3when rhat<2^31,2when rhat<2^32, and1otherwise. Every
continuing correction adds normalized vtop≥2^31 to rhat<2^32 without64-bit
overflow; all other paths clear again. This should give≤3loop-body ticks
(≤2actual corrections) using ClockCost.ranked_loop. The argument has not
yet been formalized. Remaining wide-division numeric/physical contracts,
Taylor, current parent-header validation/execution/wrappers/main, uniform
target composition, dominant-slack review and final cleanup stay open.


## Literal quotient correction: three ticks and exact two-digit arithmetic

The original divmnu again-loop is extracted syntactically and its actual
clear/compare/decrement/add/set instructions have a checked execution model.
With normalized vtop in[2^31,2^32), its current-state rank is at most3 and
strictly decreases at every real continuing body. Its whole loop costs≤3
source ticks on every outcome, including exhausted clocks; there are at
most2actual corrections on any normal exit. The loop preserves all
nonlocal fields. No completed loop trace or future helper is an entry premise.

The unsigned correction comparison prevents decrementing qhat=0. Each real
correction therefore subtracts exactly1naturally and adds exactlyvtop to
rhat without64-bit wrap. The actual normal-exit proof derives its finite
Trace, exact qhat/rhat/count conservation, zero again flag and failed final
correction guard. Trace.preserves transports mathematical invariants through
that same actual history. For genuine32-bit quotient/second/low digits, the
word guard is exactly rhat*2^32+low<qhat*second, including its room test.

Starting with an upper quotient estimate, this actual history returns the
exact quotient for a two-digit divisor and the exact natural remainder
rhat*2^32+low-qhat*second. The ordinary div64by32 initial estimate is proved
upper from its real remainder<top; the original max-digit initialization is
proved upper and conserving on its genuine digit-sized numerator range.
Their actual surrounding caller/array states still need connection. This
is not yet a complete divmnu or wide-division contract.

For Taylor, numerical division can specialize to at most2divisor digits
during the first1280iterations:1280*11684671=14956378880<2^34. This inspected
plan avoids general8-digit quotient correctness; general runtime still needs
all actual reached helper paths. The actual Taylor counter/denominator and
physical workspace facts must be connected before applying this reasoning.

Validation: current-qhat-normal-v1.log PASS980jobs and
current-qhat-quotient-v2.log PASS980jobs; printed axioms permitted. Final log
covers all current source facts including the strengthened trace conclusion.
Index8700modules/18335facts; inventory8745/replacement closure0/fixed files
unchanged. Claim infinity; no global finite target K or full verifier success.
Overall estimate remains50%, plausible40–60%. Usage29%weekly/0resetcredits,
ordinary usage allowed. No executable or challenge hypothesis changed.

Next: real u256_to_digits/digits_len images and leading nonzero digit,
normalization stores and digit-array division. The actual640-byte u256_ws
allocation/global still must be retained from startup through main. The
one-digit path can use the checked div64by32 helper. Two-digit quotient
correction now has its numerical contract; its two subtraction/store steps
still must construct the next real remainder image. Taylor/current parent
header validation/execution/wrappers/main, uniform target composition,
dominant-slack review and cleanup remain open in the same active goal.


## Actual u256_to_digits physical image and ignored caller

A checked physical word-slot image now models up to16distinct workspace
slots, with exact prefix writes and preservation of every cell outside the
write set. Its mapped-slot entry facts follow from the current ordinary
64-byte arena and alignment, without assuming initialized contents. The
eight converted base2^32digits are each below2^32, and their natural
little-endian value equals the real four-limb input. Each32-bit digit is
stored in an8-byte source word slot.

The unchanged u256_to_digits(58) literal eight-store body now has exact
ordered execution at every body clock, including0. It returns0, constructs
the real digit image and changes only memory/local return state. The full
body allowance is0source ticks; the actual p-word/a-quad ABI and ignored
caller are checked at1source tick. A real normal caller derives its own
funding and exact canonical returned state. Every memory cell outside the
64-byte nonwrapping buffer is protected. No future store/helper outcome is
an entry premise; actual mapped destinations come from the current arena.

Validation: current-wide-digits-image-v2.log PASS1020jobs,
current-wide-digits-stores-v1.log PASS1020jobs and
current-wide-digits-call-v1.log PASS1021jobs; printed axioms permitted.
Index8700modules/18354facts; inventory8745/replacement closure0/fixed files
unchanged. Claim infinity; no global finite target K or full verifier success.
Overall estimate remains50%, plausible40–60%. Usage30%weekly/0resetcredits,
ordinary usage allowed. No executable or challenge hypothesis changed.

Next: actual digits_len(60), deriving its returned count≤8, nonzero leading
digit and zero suffix from this same physical image, including short-clock
outcomes and real early returns. digits_to_u256(59) then needs its actual
read/combination inverse to the image. The divmnu one-/two-digit numerical
paths still need their real array stores/next remainder model.
CurrentStartup has the real u256_ws_init allocation and scalar/global
frameworks; derive and retain its640-byte allocation/global through startup
and main. The older MainU256Prefix has obsolete concrete startup cursors,
so do not infer the current address from that older main template. Only
workspace ownership/global/domain are needed initially, not old contents: the
real conversion and clearing calls initialize used slots. Taylor/current
parent-header validation/execution/wrappers/main, uniform target composition,
dominant-slack review and cleanup remain in the same active goal.


## Actual digits_len: physical scan, early returns and exact caller charge

The unchanged digits_len(60) now has an exact execution theorem at every
clock for the real initialized mapped digit image, for counts at most8.
It reads the actual descending cells and either returns the genuine last
nonzero index plus1 or times out with exhausted clock. Its scan count tracks
early returns; it costs at most the original count body source ticks and
at most count+1 for the actual ordinary caller, before its continuation.
No normal return or future funding is assumed to establish that allowance.

A real normal body return derives its own required scan funding, exact
returned word and full nonlocal/remaining-clock frame. The returned count
is at most8, positive for a nonzero represented number, identifies a
nonzero leading digit and leaves a zero suffix. Trimming to it preserves
the represented natural number. The real p/n scalar ABI, funded scoped
execution and actual normal child resumption are checked. Child resumption
does not infer the caller's own call funding when the scan count is0;
that tick remains the obligation of the actual scoped-call execution.

Validation: current-digits-length-call-v1.log PASS1022jobs; all16new printed
facts have only permitted axioms. Index8700modules/18370facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Overall effort estimate
remains50%, plausible40–60%. Usage30%weekly/0resetcredits, ordinary usage
allowed. No executable or fixed challenge assumption changed.

Next: actual digits_to_u256(59) mapped reads/word combination and numeric
inverse; then real one-/two-digit divmnu array stores and next remainder
image. Derive and retain the current640-byte u256_ws allocation/global from
startup, then connect Taylor/current parent-header validation/execution/
wrappers/main. Uniform target composition, exact K evaluation,
dominant-slack review and final cleanup remain in the active goal.


## Actual digits_to_u256 reconstruction and caller

The unchanged digits_to_u256(59) now reads the eight real mapped cells and
returns the exact four-word tuple produced by its literal OR/left-shift
expressions, at every body clock including0. It spends0body source ticks,
and its actual unary scalar/four-word-return ABI prices the ordinary caller
at1tick before the continuation, on every outcome. A funded real caller
resumes with the exact tuple and unchanged physical state; the actual normal
child-return contract supplies that same continuation without inventing
funding for the caller's separate tick.

For genuine32-bit digits, the returned tuple's natural value equals the
little-endian digit-array value. Converting any real four-word input to
digits and reconstructing it returns exactly the original four words.
These are checked actual read/shift/OR and arithmetic contracts, not an
assumed numerical wide-division oracle. The full divmnu/wide-division
contract and its current startup workspace entry remain open.

Validation: current-digits-to-words-call-v2.log PASS1022jobs; all11new printed
facts have only permitted axioms. Index8700modules/18381facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Overall effort estimate
remains50%, plausible40–60%. Usage30%weekly/0resetcredits, ordinary usage
allowed. No executable or fixed challenge assumption changed.

Next: actual one-digit divmnu descending loop and its real quotient stores/
remainder return, using the checked div64by32 scalar helper and the digit
images. Then two-digit normalization, subtraction/store and next remainder
images. Derive/retain the current640-byte u256_ws allocation/global from
startup before connecting actual Taylor/header validation/main. Uniform
target composition, exact K, slack review and cleanup remain in the same
active goal. The5historical untracked RlpLength/RlpWrite WIPs stay untouched.


## Actual one-digit divmnu loop and short-clock bound

The unchanged divmnu(61) one-digit branch and its exact original loop are
identified syntactically. Each real body decrements j, reads the actual next
input digit, invokes the checked32-round div64by32 body through its scalar
ABI, stores the genuine quotient digit and assigns the next remainder.
The actual caller costs33ticks and the outer loop adds1tick per digit.

The full descending loop now constructs the real physical quotient image,
keeps every quotient digit below2^32, carries a remainder below the divisor,
and proves the exact natural quotient/remainder equations. Input/quotient
slot separation retains all future input reads. Every cell outside the
written quotient slots survives. The complete loop costs at most34*count
source ticks (at most272for8digits) on every outcome, including short clocks.
Its actual normal exit derives its own full funding and exact remaining
clock; no future completed helper or loop is supplied as an entry assumption.

A small reusable normal_from_zero_clock fact applies the pinned evaluator's
existing evaluate_add_clock_or_timeout theorem: a checked exact-charge run
that ends at clock0 determines the funding/result/frame of any actual
non-timeout run. This avoids repeating call/loop inversion just to derive
funding, without changing source semantics or adding assumptions.

Validation: current-single-digit-normal-v1.log PASS1028jobs; all13new printed
facts have only permitted axioms, including the pinned clock theorem's
transitive dependencies. Index8700modules/18394facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Overall effort estimate
remains50%, plausible40–60%. Usage30%weekly/0resetcredits, ordinary usage
allowed. Package remains exactly65536entries; no new candidate paths.

Next: connect this loop to the actual one-digit branch's declarations, initial
j=m/k=0, final remainder store and return, then the full divmnu caller. The
loop's mapped buffers/separation/divisor facts still must come from actual
conversion/clearing/workspace entries. Two-digit normalization/subtraction/
remainder stores, startup u256_ws ownership/global, actual Taylor/header/
main and uniform target-step composition remain open. Exact K evaluation,
slack review and cleanup remain in the same active goal. No executable or
fixed challenge assumption changed; historical untracked WIPs untouched.


## Complete actual one-digit divmnu function and ignored caller

The unchanged divmnu(61) now has a complete one-digit-path contract, from
its genuine six scalar arguments through both outer declarations, divisor
load, k=0/j=m setup, full quotient loop, final remainder store and early
function return. The quotient image is the exact natural quotient, and the
stored remainder is the exact natural remainder below the actual positive
32-bit divisor. Every quotient digit remains32-bit. All memory outside the
written quotient slots and remainder word survives; all other physical
fields are retained with the exact remaining clock.

The full body costs≤34*count source ticks (≤272for8digits) on every outcome,
including short clocks. Its real normal return derives its own full funding
and actual0return value. The real six-scalar ABI and ignored-result call now
have≤34*count+1ticks (≤273) allowances. A normally continuing actual caller
derives that funding and obtains its real quotient/remainder memory, exact
restored caller locals and canonical remaining clock. No completed later
helper or future funding is an entry premise.

The physical Buffers model is separated from local Entry bindings. Changing
lexical locals or a clock preserves the physical model; the real ABI derives
the six fresh callee bindings. This permits actual callers whose local
names/count variables differ from the formal names, without requiring fake
caller argument bindings. Their current mapped images, divisor bounds and
buffer separation still must be derived in the surrounding real division
wrapper and startup workspace trace.

Validation: current-single-digit-call-normal-v2.log PASS1029jobs; all12new
printed facts have only permitted axioms. Index8700modules/18406facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Overall effort estimate
remains50%, plausible40–60%. Usage30%weekly/0resetcredits, ordinary usage
allowed. No new candidate paths; package remains exactly65536entries.

Next: current workspace640-byte slot geometry and zero-fill images needed
by digits_divmod, then connect its actual one-digit caller/result to the
four-word quotient/remainder reconstruction. Two-digit normalization and
subtraction/store/remainder contracts remain open; they can use the checked
qhat correction quotient theorem. The startup u256_ws allocation/global
must be retained through main. Actual Taylor/header validation/main,
uniform target composition, exact K evaluation, slack review and cleanup
remain in the same active goal. No executable or fixed challenge assumption
changed; historical untracked RlpLength/RlpWrite WIPs stay untouched.


## Actual u256 workspace allocation, startup and decoder/root transport

The same real first five startup calls now derive u256_ws=2701134824 and
its640-byte extent ending at2701135464. The initial zero pointer comes from
main's genuine scalar declarations and survives the actual SHA/Keccak/SSZ
and MPT allocations. A normally returning u256_ws_init extracts its actual
allocator success, persistent room and exact global/post-state; no future
allocation return or aggregate room is supplied. All later initializers
preserve this pointer, and their actual completed sequence keeps the heap
at least2701135464, including the real EVM release.

The pointer now survives the actual caught decoder and complete root-entry
prefix. Shared workspace frames cover this additional key. The initializer
that writes u256_ws is explicitly restricted to preserving other keys;
legacy SSZ/MPT frame interfaces are checked with that real restriction.
This is a helper-proof key condition, not a changed source/challenge premise.

The first-three-call theorem now retains the entire derived global template,
including untouched globals. Existing SHA/Keccak workspace construction
reuses that shared result, removing duplicated allocation-call reasoning.
Source, source semantics, ROM and fixed proofs remain unchanged.

Validation: current-u256-startup-root-frame-v1.log PASS1610jobs, including
existing startup/decoder/root and hash-workspace APIs. All12new printed
facts have only permitted axioms. Index8700modules/18418facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Overall effort estimate
remains50%, plausible40–60%. Usage31%weekly/0resetcredits, ordinary usage
allowed. No new candidate paths; package remains exactly65536entries.

Next: derive mapped/disjoint word slots for the actual640-byte layout and
its literal q16/r8 zero-fill loops. The runtime Data/main continuation must
retain the new u256 pointer. In particular, the older input-pointer lower
bound2701134824 remains too weak by itself to show input/workspace separation:
use the newly proved actual startup heap minimum2701135464 when exposing the
input allocation, rather than assuming separation. Then connect the actual
one-digit division wrapper/reconstruction and two-digit normalization/
subtraction/remainder stores. Taylor/current header validation/main,
uniform target composition, exact K, slack review and final cleanup remain
in the same active goal. Historical untracked RlpLength/RlpWrite WIPs untouched.


## Current workspace slots and wider one-digit callers

The actual640-byte layout now has checked mapped/aligned arenas and
pairwise disjoint word slots for normalized numerator offset0/17words,
normalized divisor144/8, quotient216/16, remainder352/8, numerator424/16
and divisor560/8. Separation uses modular address cancellation and the
small literal offsets, so no unproved pointer-wrap assumption is needed.
The actual startup-derived constant pointer plus ordinary domain supplies
its arena/mapping context. Current slot geometry derives all one-digit
Buffers mapping/separation conditions from the actual input/divisor cells;
no future helper execution is assumed.

Inspection found additional original digits_divmod callers with10and16
numerator digits in the crypto helpers. The existing digits_len and full
one-digit divmnu body/caller proofs now cover up to16digits, including real
early returns, short clocks, exact normal funding and numerical/memory
results. The general one-digit caller allowance is34*count+1, hence545for16
digits and273for the8-digit Taylor/u256 path. Normalized numerator capacity
is17words for the wider actual input; the earlier9-word description covered
only the8-digit path. No executable or fixed challenge assumption changed.

Validation: current-u256-slot-geometry-wide-v1.log PASS1029jobs; all10new
printed geometry facts and all generalized prior scan/divider facts have
only permitted axioms. Index8700modules/18428facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Overall effort estimate
remains50%, plausible40–60%. Usage31%weekly/0resetcredits, ordinary usage
allowed. No new candidate paths; package remains exactly65536entries.

Next: exact literal q16/r8 zero-fill loops and their physical images, then
digits_divmod's actual one-digit caller/result and reconstruction. The
new startup heap minimum2701135464 must be carried through the actual input
allocation to prove input/workspace separation, and the u256 pointer must
enter runtime Data. Two-digit normalization/subtraction/remainder stores,
Taylor/current header validation/main, uniform target composition, exact K,
slack review and cleanup remain in the same active goal. Historical
untracked RlpLength/RlpWrite WIPs stay untouched.


## Literal quotient/remainder clearing and real tail reconstruction

The original digits_divmod(62) q16/r8 loops are extracted from the actual
Software AST. Their exact zero-store/index-increment bodies and full loops
now have checked execution models, with no incoming memory-content premise.
Each loop costs its remaining counter distance on every outcome, including
short clocks (16and8ticks from their real zero index). A genuine normal
exit derives its own required funding and exact physical post-state.

Every cleared slot is zero. Cells outside the actual write range survive,
and the initialized image of any distinct workspace buffer survives the
clear. The workspace global/domain/arena context and every other live local
binding are retained. These facts use the checked physical slot separation;
no future store/loop/helper outcome is an entry premise.

The actual digits_to_u256 tail-call form, used by both wrapper return paths,
also now has its exact four-word value/frame,1caller-tick all-outcome bound
and genuine normal-return funding contract. The existing scoped-call API
remains checked. Straight-line target work is still separate from these
source-clock allowances.

Validation: current-digit-clear-tail-return-v2.log PASS1029jobs; all19new
printed facts have only permitted axioms. Index8700modules/18447facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Overall effort estimate
remains50%, plausible40–60%. Usage31%weekly/0resetcredits, ordinary usage
allowed. No new candidate paths; package remains exactly65536entries.

Next: use the real zero images and one-digit divider's frame to reconstruct
the full quotient/remainder buffers and connect the unchanged digits_divmod
one-digit tail and whole wrapper. Retain u256 in runtime Data and derive
input/workspace separation from actual startup heap minimum2701135464.
Two-digit normalization/subtraction/remainder stores, Taylor/current header
validation/main, uniform target composition, exact K, slack review and
cleanup remain in the same active goal. Source/semantics/ROM/fixed proofs and
historical untracked RlpLength/RlpWrite WIPs remain untouched.


## Actual one-digit quotient/remainder reconstruction and wrapper tail

The real one-digit divmnu caller's quotient prefix now combines with its
previously cleared suffix to form the full16-word quotient image. Its final
remainder store combines with the old zero higher cells to form the real
8-word remainder image. The four returned words reconstruct that exact
remainder. For the actual≤8-digit u256 path, reconstructing the quotient
also gives the exact natural quotient. Wider callers retain their full
quotient image without incorrectly identifying a low256-bit read with the
whole wider quotient.

The original digits_divmod post-clearing tail is identified literally from
the current AST. Its real divmnu call and digits_to_u256 tail return now have
exact execution and actual normal-return contracts: the same observed run
derives both calls' funding, physical result and canonical remaining state.
Its all-outcome source allowance is34*count+2 (274for8digits,546for16).
No future completed call or numerical-result oracle is an entry premise.
The zero remainder image is a preceding clearing fact, not a future outcome.

Validation: current-single-digit-tail-normal-v1.log PASS1030jobs; all10new
printed facts have only permitted axioms. Index8700modules/18457facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Overall effort estimate
remains50%, plausible40–60%. Usage31%weekly/0resetcredits, ordinary usage
allowed. No new candidate paths; package remains exactly65536entries.

Next: connect the real post-scan i declaration, q16 clear, mm<n guard,
i reset and r8 clear to this tail, then the actual conversions/length calls
and complete digits_divmod/u256_divmod caller. The mm<n branch returns from
u directly; r need not have been cleared on that path. Original m=4 callers
still run u256_to_digits and initialize8cells; preserve those cells for that
return rather than assuming only4reads. Retain u256 in runtime Data and
prove input/workspace separation using startup heap minimum2701135464.
Two-digit normalization/subtraction/remainder stores, Taylor/current header
validation/main, uniform target composition, exact K, slack review and
cleanup remain in the active goal. No executable/fixed challenge premise or
historical untracked RlpLength/RlpWrite WIP changed.


## Complete real post-scan one-digit division wrapper

The actual digits_divmod i declaration, q16 clear, mm<n guard, index reset,
r8 clear, divmnu call and final tail return now have one complete checked
execution contract. The zero-numerator path really returns from u before
clearing r. The positive path retains the full16-word quotient and exact
natural remainder, with only the actual quotient/remainder buffers writable.
A real normal return derives its own funding and all of these physical facts.
Every outcome, including short-clock timeouts, spends at most17source ticks
when the scanned length is0, otherwise34*length+26 (298at8,570at16).
These are source-clock allowances, not the final target evaluator bound.

Validation: current-divmod-clearing-normal-v1.log PASS1030jobs; all10new
printed facts have only permitted axioms. Index8700modules/18467facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Effort estimate remains
50%, plausible40–60%. Usage31%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays exactly65536entries.

Next: connect the original wrapper's three pointer declarations, divisor
conversion and actual length scans, then its u256 caller. Retain u256 in
runtime Data and derive input/workspace separation using the actual startup
heap minimum2701135464. Two-digit normalization/subtraction/remainder stores,
Taylor/header validation/main, uniform target composition, exact K, dominant
slack review and cleanup remain open. No executable/fixed challenge premise
or historical untracked RlpLength/RlpWrite WIP changed.


## Complete actual one-digit digits_divmod and real caller ABI

The full unchanged digits_divmod62 function now has execution, all-outcome
source cost and genuine normal-return contracts on the one-digit-divisor
path. The proof executes the q/r/v pointer declarations, real divisor
conversion, both actual length scans and the complete preceding post-scan
wrapper. Physical input images and the derived workspace separation protect
the numerator through the actual divisor writes. The early return retains
its eight real numerator reads. This contract covers initial counts8–16;
it deliberately makes no claim about m=4 callers' extra early-return reads.

Normal execution derives its own funding, full16-word quotient image,32-bit
quotient digits, exact natural quotient/remainder, actual returned four-word
value and all memory outside the q/r/v write ranges. No completed helper
outcome is an entry premise. The real mixed scalar/quad ABI, original code
lookup, ordinary call pricing and actual returned-child continuation are
checked. The descending scan and returned length share their digit range,
so the full allowance is≤34*count+38:310body source ticks at8digits,311
including the caller tick (582/583at16). Source clocks still exclude the
straight-line target work required by the final task.

Validation: current-divmod-whole-caller-final-v1.log PASS1030jobs; all24new
printed facts have only permitted axioms. Index8700modules/18491facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Effort estimate remains
50%, plausible40–60%. Usage32%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays exactly65536entries.

Next: connect the complete u256_divmod/u256_div outer paths and derive the
two-digit Taylor division path's normalization, actual subtraction and
remainder stores. Retain u256 in runtime Data and derive input/workspace
separation using the actual startup heap minimum2701135464. Taylor/header
validation/main, uniform target composition, exact K, dominant slack review
and cleanup remain open. No executable/fixed challenge premise or historical
untracked RlpLength/RlpWrite WIP changed.


## Current256-bit comparison value and dependency cleanup

The actual u256_lt result now agrees with the complete natural256-bit
values:1iff a<b,0iff b≤a. Its existing physical execution and real scoped
caller remain checked. The proof uses each real64-bit limb bound, not an
assumed mathematical comparison result.

The helper now imports its actual equality/ABI and declaration dependencies
instead of the old arithmetic umbrella, which pulled unrelated stale EVM
proofs into this current path. The shared pure_value_execute fact is now
generic in the host-memory type; this removes an accidental Guest.HostMemory
import dependency without weakening its exact execution statement.

Validation: current-u256-less-number-v2.log PASS742jobs, including the real
scoped caller and generic return helper; both new facts have only permitted
axioms. Index8700modules/18493facts; inventory8745/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verifier
success. Effort estimate50%, plausible40–60%. Usage32%weekly/0resetcredits,
ordinary usage allowed. No new candidate paths; package stays65536entries.
Next: complete the actual u256 division wrapper, the two-digit Taylor path,
actual runtime workspace/input separation, Taylor/header/main and uniform
target composition, exact K, dominant slack review and cleanup. Historical
untracked RlpLength/RlpWrite WIPs and executable/fixed premises are untouched.


## Actual scoped divider and complete wide u256 quotient/remainder branch

The real scoped digits_divmod call now executes its original mixed ABI,
installs the returned four-word remainder in the caller's r binding and
resumes any actual continuation. Its physical caller model retains the
complete quotient image and exact natural quotient/remainder.

The unchanged u256_divmod63 wide branch is identified literally in the
current AST. The proof executes its actual u pointer declaration, numerator
conversion, scoped digits_divmod call, quotient reconstruction and eight-word
return. On the one-digit-divisor path its complete body costs≤313source
ticks on every outcome. Real normal returns derive their own funding, exact
natural quotient/remainder, actual returned eight words and memory frame
outside the original u/q/r/v stores. No future helper return/value is an
entry premise. Outer comparison/scalar branches remain separate work.

Validation: current-u256-wide-branch-v1.log PASS1030jobs; all8new printed
facts have only permitted axioms. Index8700modules/18501facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage32%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: complete actual u256_divmod/u256_div outer comparison and scalar
shortcut, then the two-digit Taylor path. Actual runtime workspace/input
separation, Taylor/header/main, uniform target composition, exact K,
dominant slack review and cleanup remain open. Historical untracked
RlpLength/RlpWrite WIPs and executable/fixed premises stay untouched.


## Complete actual one-digit u256 division and Taylor assigned-call form

The complete unchanged u256_divmod63 function now has an actual execution
contract for every256-bit numerator and positive32-bit divisor. Its real
zero guard and u256_lt call select the genuine a<b return,64-round scalar
shortcut or wide digits branch. Each selected path has exact clock funding,
actual eight returned words, natural quotient/remainder and full memory frame.
A genuine normal return derives these facts from the real function entry.
The total all-outcome source bound is314body ticks.

The unchanged u256_div64 wrapper now calls that actual function, extracts
its real quotient and returns the exact four-word value. Its all-outcome
bound is315body/316ordinary caller source ticks. The assigned-call form
used by Taylor derives its own funding and canonical next accumulator from
the actual normal call, together with exact natural division and protection
outside the u/q/r/v write ranges. No future callee result, value oracle or
preassumed successful assignment is an entry premise. The caller's actual
normal return supplies the assignment's type/lookup facts. Source clocks
still exclude the straight-line target work required by the full goal.

Validation: current-u256-divide-assigned-v2.log PASS1122jobs; all17new
printed facts have only permitted axioms. Index8700modules/18518facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage32%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: retain the real u256 workspace through runtime Data and derive input/
workspace separation using startup heap minimum2701135464; complete the
two-digit Taylor divisor path's normalization, actual subtraction and final
remainder stores. Taylor/header/main, uniform target composition, exact K,
dominant slack review and cleanup remain open. Historical untracked
RlpLength/RlpWrite WIPs and executable/fixed premises stay untouched.


## Actual u256 workspace pointer retained through the main prefix

The current31-helper root-hash graph now retains u256_ws on every outcome,
using the existing checked current startup/helper frames. WorkspaceEntry.main
derives its actual2701134824pointer from the same startup/decoder/root trace.
Actual root allocation and hashing retain this field at the real caller.

The runtime Data contract now carries that concrete pointer through the
actual header validation, databases, state initialization, payload-header
hashing, transaction/withdrawal tries, request encoding/hashing and version
check. Every input-data transport supplies its preserved global from the
same real call/frame. The previously proved before-validate_header prefix
and its479872713926source allowance replay with the stronger data model.
No extra workspace pointer premise was added to the whole-source entry.

Validation: current-u256-runtime-global-v1.log PASS3100jobs, including the
complete current TransactionData main-prefix theorem; permitted printed
axioms. Claim infinity; no global finite target K/full verifier success.
Effort estimate remains50%, plausible40–60%. Usage32%weekly/0resetcredits,
ordinary usage allowed. No new candidate paths; replacement closure0 and
fixed files unchanged. The package stays65536entries.

Next: strengthen the selected actual input allocation lower bound from the
real startup heap minimum2701135464 and retain its separation geometry in
runtime Data. Then connect arithmetic memory frames, complete two-digit
Taylor normalization/subtraction/remainder stores, Taylor/header/main,
uniform target composition, exact K, dominant slack review and cleanup.
Historical untracked RlpLength/RlpWrite WIPs and executable/fixed premises
stay untouched.


## Actual main-derived input/workspace separation

The selected stateless decoder run now retains the actual copied-input
lower bound2701135464, derived from the real initialized u256 allocation
and the same preceding heap/setup/input-allocation execution. Whole-source
main/root cuts use U256Workspace.main_cells to supply this bound; no extra
separation premise was added to those source-observation statements.
Older SSZ-only consumers receive the proved weaker bound explicitly.

Runtime Data now retains this copied-input lower bound and the actual
stateless-record-after-input ownership. Its existing normal frames carry
both through the full main prefix. The concrete mapped u256 context is
obtained from that same Data's actual global/domain. The complete640-byte
workspace and every real buffer word end before copied input, SI and payload
records. This includes all16quotient slots and the17normalized numerator
slots; no pointer-wrap or distinct-buffer premise is supplied by a future run.

Validation: current-u256-input-separation-v3.log PASS3100jobs, including
actual main before-validate_header and all4new printed facts; only permitted
axioms. Claim infinity; no global finite target K/full verifier success.
Effort estimate remains50%, plausible40–60%. Usage33%weekly/0resetcredits,
ordinary usage allowed. No new candidate paths; replacement closure0/fixed
files unchanged, package65536entries.

Next: use the actual stronger input boundary to transport decoded data
through arithmetic's legitimate workspace writes, and connect the completed
one-digit assigned division contract. Two-digit Taylor normalization,
subtraction/remainder stores, Taylor/header/main, uniform target composition,
exact K, dominant slack review and cleanup remain open. Historical untracked
RlpLength/RlpWrite WIPs and executable/fixed premises stay untouched.


## Decoded-data transport through actual arithmetic workspace writes

Copied-input, witness-array and complete runtime-data frames now accept a
proved physical lower boundary. Their existing APIs delegate to these shared
proofs at the older boundary; no earlier main/hash/header contracts were lost.
The new workspace metadata frame uses the actually derived2701135464cutoff,
so arithmetic may legitimately write its allocated640-byte workspace.

Data.after_one_digit_division now connects the completed original assigned
u256_div contract directly to the same reached runtime Data. An actual normal
call derives its required clock, exact quotient and real destination binding,
and retains SI/gas/payload, copied bytes, witness/request images, heap and all
workspace globals. Its earlier-memory frame follows from the actual u/q/r/v
stores and checked workspace geometry; no future memory frame or normal
helper result is supplied as an entry premise. The assigned destination is
statically distinct from SI, as it is at the real Taylor accumulator call.

Validation: current-u256-data-memory-frame-v1.log PASS3100jobs, including
complete current before-validate_header main prefix and all5new printed facts;
only permitted axioms. Index8700modules/18527facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K or
full verifier success. Effort estimate remains50%, plausible40–60%.
Usage33%weekly/0resetcredits, ordinary usage allowed. No new candidate paths;
package stays65536entries.

Next: complete the actual two-digit Taylor divisor path, including physical
normalization, corrected quotient, subtraction and remainder stores, then
connect Taylor/header/main and uniform target composition. For two-digit
divisors the checked correction theorem gives the exact digit quotient;
prove its connection to the actual subtraction before claiming that the
add-back branch cannot execute. Exact K, dominant slack review and final cleanup remain.
Historical untracked RlpLength/RlpWrite WIPs and executable/fixed premises
stay untouched.


## Actual two-digit subtraction arithmetic and physical inner body

The original multiply/subtract digit now has a checked exact conservation
law,32-bit output/carry bounds and signed64-bit no-overflow justification.
The actual product of two32-bit factors supplies its own product cap.
Two such real digit operations with an exact quotient leave a zero top
word and reconstruct the ordinary natural remainder. This is arithmetic;
the original quotient-correction caller must still supply that exact quotient
before the actual add-back branch can be ruled out.

The unchanged divmnu61 subtraction step is identified literally in its AST.
From the actual mapped UN/VN cells and existing qhat/k/i/j bindings, its
original p/t declarations, loads, low-word store, signed carry update and
index increment execute exactly. Both temporary variables are genuinely
restored; all other bindings and fields are retained, and memory changes
only at the intended normalized-numerator word. No future run/result is an
entry premise. Its source-clock cost is0because it has no calls or loops;
its straight-line target cost remains part of the unfinished global task.

Validation: current-two-digit-subtract-store-v4.log PASS1122jobs, all19new
printed facts use only permitted axioms. Index8700modules/18546facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage33%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package remains65536entries.

Next: connect both actual subtraction iterations, derive their two source
loop ticks and physical stores, then connect the real corrected quotient
and top-word update. Two-digit normalization/remainder stores, Taylor/header/
main, uniform target composition, exact K, dominant slack review and final
cleanup remain open. Historical untracked RlpLength/RlpWrite WIPs and
executable/fixed challenge premises remain untouched.

## Complete actual two-iteration normalized subtraction loop

The original n=2 subtraction loop now executes both actual iterations and
its final false guard from the real UN/VN images. The first real store
preserves the next input digit and divisor digit by checked workspace
nonaliasing, including the seventeenth normalized numerator slot. Its actual
outgoing32-bit carry supplies the next iteration's entry invariant.
The complete final state has exactly the two original low-word stores,
real i/k bindings, unchanged other locals/fields and clock reduced by2.
Every outcome costs≤2source loop ticks, including short-clock timeouts.
Actual normal returns derive both required ticks from the pinned clock
theorem; their funding is not assumed.

The physical final carry/cells are connected to the checked remainder
arithmetic when supplied the corrected quotient. This theorem explicitly
retains that quotient premise until the actual surrounding correction
caller establishes it. No global no-add-back claim is made yet. Source
clocks still omit straight-line target work.

Validation: current-two-digit-subtract-loop-v4.log PASS1122jobs, all11new
printed facts have only permitted axioms. Index8700modules/18557facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage33%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries. Shared private one-step/exit
composition keeps the kernel proof small: the final build took65seconds
with2.2GiB maximum resident memory under the existing8GiB host guard.

Next: connect the actual corrected quotient to these subtraction cells and
the actual top-word/quotient stores, then two-digit normalization and final
remainder extraction. Taylor/header/main, uniform target composition, exact
K, dominant slack review and final cleanup remain open. Historical untracked
RlpLength/RlpWrite WIPs and executable/fixed challenge premises stay untouched.


## Actual quotient correction connected to subtraction and final digit stores

The full original phase inside again's scope is now identified literally:
actual quotient correction, k declaration, i reset, both subtraction
iterations, tt declaration and unchanged complete add-back conditional.
Actual correction normal returns retain all untouched caller bindings and
the real normalized workspace window. They derive the exact current qhat
from the initial estimate's conservation/upper-bound facts; the subsequent
subtraction no longer receives a future corrected-quotient oracle premise.

The real tt read is then zero. Its signed guard selects the original
nonnegative branch, which stores the actual quotient digit and zeroes the
actual top word. Both lexical k/tt restorations are included. Normal phase
returns derive their subtraction funding, exact natural remainder and
exact four-store physical memory update, while every other source field
is retained. The complete literal phase costs≤5source ticks on every
outcome; timeouts and failed paths are included. Straight-line target
work remains unpriced by these source clocks.

Entry facts still include the initial estimate's conservation and upper
bound, current normalized physical images and normalized leading-digit
range. The preceding actual estimate branch/normalization must derive
those facts; no whole two-digit divider or main theorem is claimed here.
Static AST selection was narrowed to the real expression/guard shapes,
removing a redundant list of constant-name inequality proofs.

Validation: current-two-digit-corrected-v2.log PASS1122jobs; all11new
printed facts have only permitted axioms. Index8700modules/18568facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage33%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: derive the initial estimate/conservation/upper bound from the original
max-digit/scoped div64by32 branches. Connect physical normalization, outer
quotient/remainder loop invariant and final remainder extraction, then the
actual two-digit caller/Taylor/header/main. Uniform target composition,
exact K, dominant slack review and final cleanup remain open. Historical
untracked RlpLength/RlpWrite WIPs and executable/fixed premises stay untouched.

## Real initial quotient estimate and complete original per-digit phase

The original maximum-digit branch and scoped div64by32 estimate are now
identified literally and executed with their actual caller assignments.
The scalar call derives both actual returned words and its33ticks from
a genuine normal callee run, then restores the real qr binding. The maximum
branch uses its actual wrapped remainder expression. Both branches derive
initial estimate conservation and the upper estimate for the same physical
three-digit/two-digit window; no future corrected quotient is assumed.

These original branches are now connected through the actual again scope
to quotient correction, carry/index initialization, both subtraction
iterations and the real quotient/top-word stores. The complete literal
per-digit phase costs≤38source ticks on every outcome, including failed
and short-clock prefixes. A genuine normal phase derives its exact quotient,
natural remainder, complete four-store memory update and all other source
fields. Checked workspace geometry retains both low remainder words, the
quotient digit and zero top word; every other word is protected.

The entry still describes the actually normalized physical window, captured
ujn/ujn1/ujn2 and vtop/vsec bindings, fresh zero qhat/rhat bindings and the
outer-loop invariant window<divisor*2^32. Normalization/capture/outer-loop
execution must derive these current-entry conditions. The whole two-digit
divider, Taylor, main and global target bound remain unfinished. These
source clocks still omit the straight-line target work.

Validation: current-two-digit-estimate-phase-v3.log PASS1126jobs; all11new
printed facts use only permitted axioms. Index8700modules/18579facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage34%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: actual two-digit normalization and the outer descending quotient loop,
including captured digit loads, preserved prefix/suffix images and the
window-range invariant; final remainder extraction and complete caller.
Then Taylor/header/main, uniform target composition, exact K, dominant slack
review and final cleanup. Historical untracked RlpLength/RlpWrite WIPs and
executable/fixed challenge premises remain untouched.

## Exact actual normalization arithmetic for complete digit arrays

The original left-shift/right-shift/or/mask expressions now have exact
natural32-bit carry equations for every s≤31, including s=0. Both64-bit
shifted intermediates are justified without overflow. The right-shifted
carry is below2^s; a leading digit whose actual shifted value is below2^32
has zero outgoing carry, exactly the checked nlz32 upper-bound case.

These real word equations now telescope across every digit prefix. The
normalized numerator image, including its genuine extra carry word,
represents U*2^s exactly and every represented word remains32-bit.
The normalized divisor's actual leading bound removes its outgoing carry,
so its stored n-word image represents D*2^s exactly. No zero numerator-top
assumption or replacement arithmetic implementation is used.

This is the numerical bridge. The physical descending normalization loops,
actual nlz32 caller, mapped input/output images and following outer loop
still must establish the same image at runtime. No full two-digit divider,
Taylor/main allowance or global target bound follows yet.

Validation: current-normalization-array-number-v2.log PASS1126jobs; all9new
printed facts have only permitted axioms. Index8700modules/18588facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage34%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: execute the actual VN and UN normalization loops and their separate
first/top-word stores. Derive s and the leading bounds from the actual
nlz32 call. Then actual captured digit loads and the outer-loop invariant:
initial window<divisor*2^32 follows from the original m-digit input bound
and D≥2^32; after a real digit phase, the next window is its untouched
low digit plus2^32 times the proved remainder<divisor. Prove this against
the actual prefix/suffix images and quotient stores. Final remainder
extraction and caller/Taylor/header/main, uniform target composition, exact
K, dominant slack review and cleanup remain. Historical untracked WIPs and
executable/fixed premises stay untouched.


## Literal physical normalization loops, source cost and output frames

Both original VN and UN descending normalization loops are now identified
literally. Their shared original body performs the two actual mapped digit
loads, checked variable shifts, OR/mask store and exact i decrement. The
32-s expression and all actual shift guards are derived from s≤31; s=0
is included. Actual workspace geometry derives mapped slots and separation.

Normal loop completions retain the input image after every real output store,
include the final false guard, write every positive index through incoming
i and finish with i=0. All other local bindings and every nonmemory source
field are retained. Their exact normal cost is incoming i; every stopped/
short-clock outcome costs≤i. Real normal returns derive their own funding
from the pinned clock theorem. The exact recursive store image and memory
outside those positive indices are checked. The separately stored UN top
word survives, including the seventeenth normalized slot at length16.

These loop entries describe actual input images, mapped/disjoint buffers,
current pointer/i/s bindings and lengths≤16. The earlier caller still must
derive them, execute the separate lowest/top-word stores and connect the
nlz32 result before assembling the complete normalization prefix. These
source-loop ticks still omit straight-line target work.

Validation: current-normalization-physical-loop-v3.log PASS1126jobs; all15new
printed facts use only permitted axioms. Index8700modules/18603facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage34%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: original separate VN/UN lowest-word and UN extra-top stores, actual
nlz32 call and counter initialization, complete normalization images/values
and frame. Then captured digit loads, outer descending quotient loop with
its current window-range/prefix/suffix invariant, final remainder stores
and actual two-digit caller/Taylor/header/main. Uniform target composition,
exact K, dominant slack review and final cleanup remain. Historical untracked
RlpLength/RlpWrite WIPs and executable/fixed premises stay untouched.


## Complete physical normalization array blocks and boundary stores

The original separate VN/UN lowest-word stores and extra UN[m] carry store
are now identified literally and executed with their real loads, variable
shifts, masks and mapped destinations. The extra store admits the actual
seventeenth normalized numerator slot. They consume0source call/loop ticks.

Counter initialization, the complete original descending loop and the
separate lowest-word store now form one checked array block. Actual normal
completion derives its own length-1funding and complete physical normalized
image, exact clock and static-field frame. Every stopped/short-clock outcome
costs≤length-1. The original right-associated continuation syntax resumes
from that same proved state using a checked semantic sequence identity;
no executable bytes are reassociated or replaced.

The post-state retains all locals except i, sets i=0 and retains the actual
allocated workspace context. Its complete write range is checked. The extra
numerator carry survives the whole block, including the lowest-word store
and the seventeenth-slot case. The incoming input image/pointer/s/count
premises remain obligations of the earlier actual normalization caller.

Validation: current-normalization-complete-array-v2.log PASS1126jobs; all16new
printed facts have only permitted axioms. Index8700modules/18619facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage34%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: connect the actual nlz32 return to both array blocks and the intervening
extra-top store. Derive their entries from actual n/m/u/v/un/vn bindings and
mapped input images, then expose the real vtop/vsec/outer-loop continuation.
Actual captured digit loads, outer-loop range/prefix/suffix invariant, final
remainder extraction and complete two-digit caller/Taylor/header/main remain.
Uniform target composition, exact K, dominant slack review and final cleanup
remain open. Historical untracked WIPs and executable/fixed premises stay
untouched; source-clock bounds still omit straight-line target work.


## Actual nlz32 caller connected to the complete normalization prefix

The original scoped s/nlz32 call and its complete right-associated two-array
normalization prefix are identified literally, with the actual later
vtop/vsec/outer-loop continuation still inside s's original scope.
Its real argument is loaded from the mapped physical V[1] of the same
current n=2 entry. The checked original nlz32 callee supplies s≤31 and both
shifted-leading-digit bounds; no future normalization result/count is supplied.

That actual returned binding now enters the real VN block, UN[m] carry
store and UN block. From the same original input images, these stages
construct a complete Ready state: original U/V retained, actual normalized
UN[m+1]/VN[2] images, real pointer/count/s bindings, i=0 and allocated context.
Their actual numbers are U*2^s and D*2^s, and the actual normalized top divisor
digit lies in[2^31,2^32). The body costs m source ticks on every outcome;
its real normal return derives its own funding. Including the actual nlz32
call, the bounded prefix costs≤m+1 and a funded actual call reaches its same
original continuation with exact remaining clock and lexical s restoration.

Only UN[0..m] and VN[0..1] are written. All other memory and all locals
except i are preserved by the body, and all other source fields remain exact.
Entry conditions are still the actual two-digit caller's m/n/u/v/un/vn/i
bindings, fixed installed code, original mapped32-bit images,2≤m≤16 and
nonzero leading divisor digit. The earlier real divmnu/digits_divmod caller
must derive those conditions. Source clocks still omit straight-line target work.

Validation: current-normalization-prefix-v2.log PASS1126jobs; all14new printed
facts have only permitted axioms. Index8700modules/18633facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage34%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: original vtop/vsec loads and outer j initialization; real three-digit
captures and qhat/rhat declarations, then the checked per-digit phase.
Use an actual two-word carried remainder at UN[j]/UN[j+1], below the actual
normalized divisor, plus the untouched lower prefix. A step consumes the
next lower digit through window=low+2^32*carry, so the existing remainder
proof derives the next carry bound. Induct over actual j, retaining the
quotient image and D*Q+R conservation; prove untouched quotient suffix and
memory frames from actual stores. The initial carry bound follows from
U<2^(32*m), D≥2^32 and the checked common normalization factor. This is the
remaining proof plan, not a checked outer-loop theorem.

Final remainder extraction, complete two-digit caller/Taylor/header/main,
uniform target composition, exact K, dominant slack review and cleanup remain.
Historical untracked WIPs and executable/fixed premises stay untouched.


## Actual per-digit local frame and original outer window loads

The actual initialized subtraction post-state now retains the outer loop's
unmodified bindings and leaves its real inner i counter at2. This is carried
through the genuine correction-loop return and complete initial-estimate/
again scope. An actual normal full per-digit phase therefore retains j and
the real pointers/counts while supplying a typed i=2 for its successor.
The proof derives these from the same actual normal traces; no future state
or successful result is supplied as an extra entry condition.

The complete current outer quotient loop is now identified literally,
including j decrement, three actual UN loads, fresh qhat/rhat declarations
and the checked per-digit phase. At an actual n=2/j window, all three real
capture expressions now read the mapped UN[j+2],UN[j+1],UN[j] words. Their
64-bit add/subtract/address arithmetic and physical slot bounds are checked.
This identifies and reads the body; it is not yet an executed full outer-loop
or complete two-digit divider theorem.

Validation: current-two-digit-outer-capture-read-v1.log PASS1126jobs; all8new
printed facts use only permitted axioms. Index8700modules/18641facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage35%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: derive the fresh captured/scalar declaration entries and execute the
real j decrement/body. Carry two actual32-bit remainder words at UN[j] and
UN[j+1], below the actual normalized divisor, plus the untouched lower input
prefix. The next window is low+2^32*carry; the actual phase derives its next
remainder and preserves all needed locals. Induct over j to produce the
quotient image and D*Q+R identity, and prove the initial carry from the
actual normalization images/number bound. Source clocks still omit target
straight-line work. Final remainder extraction, complete two-digit caller/
Taylor/header/main, uniform target composition, exact K, dominant slack
review and cleanup remain. Historical untracked WIPs and executable/fixed
premises stay untouched.

## Real outer quotient iteration and preserved carried-remainder entry

The original j decrement, three mapped captured digit loads and five lexical
ujn/ujn1/ujn2/qhat/rhat declarations now execute into the checked actual
estimate/correction/subtraction phase. Both normal and stopped outcomes keep
the original lexical restorations. The complete actual body costs≤38source
call/loop ticks; the surrounding while's own tick is separate.

Its real normal execution derives the quotient digit as the three-word
window divided by the actual normalized two-word divisor, and both written
remainder words are32-bit and represent the natural remainder. The actual
four-store memory image, all static fields, retained external locals, i=2
and decremented j are checked. No future phase result or successful funding
is supplied as an entry premise.

A physical guard entry now consists of the untouched low input prefix,
two current32-bit carry words at UN[j]/UN[j+1], actual normalized VN cells,
current pointers/counts and carry<divisor. At j=count+1 the genuine next
assignment derives the phase window from input[count]+2^32*carry, which is
below divisor*2^32. An actual normal body constructs the complete successor
entry at j=count: its new carry is the proved remainder<divisor, the entire
lower prefix and divisor image survive, and all required bindings persist.
This closes one actual iteration's invariant preservation; induction over
the full original outer loop and its quotient image/conservation remain open.

Validation: current-two-digit-outer-successor-v2.log PASS1126jobs; all12new
printed facts use only permitted axioms. Index8700modules/18653facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage35%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: full actual descending-loop cost≤39*count, quotient image and
D*Q+R conservation. Derive its initial two-word carry range from the actual
normalization images and common normalization factor. The enclosing current
vtop/vsec loads/j initialization, final remainder extraction and complete
two-digit caller/Taylor/header/main still remain. Source-clock bounds omit
straight-line target work. Uniform target composition, exact K, dominant
slack review and final cleanup remain. Historical untracked WIPs and
executable/fixed premises stay untouched.

## Full actual two-digit outer loop and derived normalization entry

The complete original descending quotient loop now has an all-outcome
source allowance≤39*incoming j: one real outer tick and≤38actual body ticks
per digit. Its physical invariant decreases at every genuine continuation;
actual errors/timeouts/stopped outcomes fit the same bound. A checked
structural frame excludes escaping return/break/continue from its real body,
including the complete original add-back syntax and scoped callees.

An actual normal full-loop evaluation now constructs every quotient digit
in physical Q, derives each digit's32-bit bound, finishes with j=0 and two
actual32-bit remainder words below the same normalized divisor, and proves
D*Q+R=initialCarry*2^(32*count)+untouchedInputPrefix. Thus its physical output
is the natural quotient and remainder. The same induction retains all
external locals and static fields, proves the exact enclosing write range,
and derives the zero UN[2] needed by the original final remainder loads.
No future successful body/helper return or incoming funding is assumed.

The actual normalized numerator's two top words are now proved below the
normalized divisor. The argument uses the real highest32-bit input digit,
the normalization carry<2^s and the original nonzero high divisor digit;
both numerator and divisor use the same actual factor2^s. This range is a
derived fact, not a loop-entry oracle. The checked normalization images now
supply the complete first guard entry after its described vtop/vsec/j bindings.
Its carry/prefix number is proved equal to the whole original numerator*2^s.
The next step must execute those actual leading loads and j assignment.

Validation: current-two-digit-outer-loop-v5.log PASS1126jobs; all6new printed facts have only permitted
axioms. Index8700modules/18659facts; inventory8745/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verifier
success. Effort estimate remains50%, plausible40–60%. Usage35%weekly/
0resetcredits, ordinary usage allowed. No new candidate paths;
package stays65536entries.

Next: actual vtop/vsec loads and j initialization connecting Ready to this
first guard; original post-loop quotient clearing, two-digit remainder
extraction/denormalization and return. Then complete current two-digit
callee/caller, Taylor/header/main, uniform target-step composition, exact K,
dominant slack review and final cleanup. Source-clock allowances omit
straight-line target work. Historical untracked WIPs and executable/fixed
premises stay untouched.

## Actual leading VN loads/counter and exact original remainder expressions

The original vtop/vsec declarations, their mapped VN[n-1]/VN[n-2] loads
and the real m-n+1 assignment to an already typed j are now identified
literally and executed at every clock. Their lexical restorations are
retained on every outcome. The actual continuation starts at the previously
proved first-guard state; no future loop result, count or funding is supplied.
The complete original leading prefix plus outer loop therefore costs
≤39*(m-1)source ticks. Its actual normal execution exposes the full physical
quotient/remainder result inside its real restored scopes.

The unchanged final remainder expressions now have checked exact natural
values: low>>s OR ((high<<(32-s)) AND mask). Both shift intermediates fit64bits,
the OR fields are disjoint, and each result is32-bit, including s=0.
Together the two genuine expressions at UN[0]/UN[1] and UN[1]/zero represent
(normalized remainder)/2^s exactly. Their physical loads, two R stores and
loop/return still must be executed.

The same actual normalized loop result now cancels the common positive
factor2^s: its quotient is original U/D, its normalized remainder is
(U%D)*2^s, and those final two original expressions represent U%D. The proof
uses the actual input-image number equations and physical loop result;
it does not assume the desired future original division result.

Validation: current-two-digit-leading-denormalize-v4.log PASS1126jobs; all8new printed facts have only permitted
axioms. Index8700modules/18667facts; inventory8745/replacement closure0/fixed
files unchanged. Claim infinity; no global finite target K/full verifier
success. Effort estimate remains50%, plausible40–60%. Usage35%weekly/
0resetcredits, ordinary usage allowed. No new candidate paths;
package stays65536entries.

Next: actual post-loop quotient clearing and two-digit remainder loads,
shifts/stores/loop/return, then assemble the current two-digit divmnu callee
and ordinary/scoped callers. Continue through digits_divmod/u256 wrappers,
Taylor/header/main, uniform target-step composition, exact K, dominant slack
review and final cleanup. Source-clock allowances omit straight-line target
work. Historical untracked WIPs and executable/fixed premises stay untouched.


## Complete physical two-digit remainder stores, loop and return

The original final two-load right-shift/left-shift/mask/OR expression now
reads the actual mapped UN[i]/UN[i+1] cells, writes the actual R[i] cell and
increments the typed original i, at every body clock. Both variable shift
guards and all three physical UN cells are checked, including s=0.

The two real final iterations and their false guard now execute exactly.
Their physical post-state writes only R[0]/R[1], retains all other locals
inside the loop and pays exactly2ticks. Every stopped/short-clock outcome
costs≤2; an actual normal loop completion derives its own funding and exact
post-state. Both stored words and the complete outside-memory frame check.

The entire original i=0 initialization, final loop and return0 are identified
literally and executed. The result includes the evaluator's genuine clearing
of locals on return. An actual returned computation derives its own2ticks,
returned0 and exact two-store memory; no future successful return or funding
is supplied as an entry oracle. The same actual preceding outer-loop result
supplies the normalized remainder words, their32-bit bounds, derived zero
UN[2], mapped context and retained un/r/n/s bindings. The intervening actual
quotient-clearing block still must be executed and retain this entry.

Validation: current-two-digit-remainder-complete-v3.log PASS1126jobs; all16new
printed facts have only permitted axioms. Index8700modules/18683facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage36%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: original post-loop j=m-n+1 assignment and trailing quotient clear;
for n=2 it executes exactly one real zero store. Retain the remainder entry
through that actual store, and compose the right-associated clear/remainder
continuation. Then assemble current two-digit divmnu normalization/outer/
return and ordinary/scoped callers. Continue through digits_divmod/u256,
Taylor/header/main, uniform target-step composition, exact K, dominant slack
review and final cleanup. Source-clock allowances omit straight-line target
work. Historical untracked WIPs and executable/fixed premises stay untouched.


## Complete original post-normalization continuation and prefix funding

At n=2 the original trailing j=m-n+1 assignment and quotient-clear loop
now execute exactly one real Q[m-1]=0 store, increment j to m and observe the
false guard. All-outcome cost≤1; normal completion derives its own funding
and exact physical post-state. The literal right-associated prefix resumes
any original continuation without reassociating executable bytes.

Actual Q/UN workspace separation proves that store retains the entire
previously derived remainder entry. The same preceding outer-loop result
supplies q/m/n and typed i/j. The complete literal quotient-clear/remainder/
return suffix now executes in3ticks and returns0 with the genuine cleared
locals and exact physical post-state. Every stopped outcome costs≤3; actual
returned outcomes derive their own funding and result.

The full original continuation after normalization is now identified
literally: leading VN captures/j initialization, complete outer quotient
loop, quotient clear, both final remainder stores and return. At every clock
and on every outcome its source allowance is39*(m-1)+3. Actual returns expose
the genuine outer-loop quotient/remainder result and exact final suffix
state inside the real restored leading scopes. All entries follow from that
same normalized image and actual loop; no future result oracle is supplied.

A generic actual non-timeout normalization-call trace now derives m+1
funding, the real nlz32 shift, complete normalized images, exact boundary
clock and actual continuation trace/restoration. The proof pads the actual
execution using the pinned evaluator clock theorem, runs the already proved
fixed prefix, and derives funding from clock monotonicity before replaying
that same real prefix at the original clock. It assumes no future
normalization result or successful funding.

Validation: current-two-digit-post-normalization-v4.log PASS1127jobs;
all14new printed facts have only permitted axioms. Index8700modules/
18697facts; inventory8745/replacement closure0/fixed files unchanged.
Claim infinity; no global finite target K/full verifier success. Effort
estimate remains50%, plausible40–60%. Usage36%weekly/0resetcredits,
ordinary usage allowed. No new candidate paths; package stays65536entries.

Next: connect the complete nlz32/normalization call to this literal suffix
and its actual normal result, then introduce the original i/j/un/vn scopes
and n=1 guard to finish the actual two-digit divmnu callee and callers.
Continue through digits_divmod/u256, Taylor/header/main, uniform target-step
composition, exact K, dominant slack review and final cleanup. Source-clock
allowances omit straight-line target work. Historical untracked WIPs and
executable/fixed premises stay untouched.


## Full unchanged two-digit divmnu body:605source ticks at width16

The complete original nlz32/normalization call now resumes the checked
literal final continuation. At n=2 and2≤m≤16 its all-outcome source allowance
is40*m-35. Actual returns derive the real shift, normalized arrays, physical
quotient-loop result, exact final suffix stores and every original s/vtop/
vsec restoration. Funding is derived from the same real non-timeout trace.

The original whole divmnu body is now connected: i/j declarations, the actual
false n=1 guard, global u256_ws reads and UN/VN declarations all execute into
that same normalized program. Their actual lexical restorations are retained
on every outcome. No incoming i/j/un/vn bindings or future normalization,
helper result or paid clock are supplied as entry premises.

The whole unchanged function therefore costs≤40*m-35source call/loop ticks
at the real two-digit divisor entry:285at m=8 and605at m=16. It assumes actual
physical original U/V images with32-bit digits, nonzero high divisor digit,
current q/r/u/v/m/n formals, installed code and the allocated workspace. The
earlier actual digits_divmod caller must derive those entries. Normal returned
runs derive returned0, the complete physical normalized-loop/final-store
state, ordinary natural quotient U/D and denormalized remainder U%D. This is
the original function, not a replacement arithmetic implementation.

Validation: current-two-digit-full-body-v3.log PASS1127jobs; all7new printed
facts use only permitted axioms. Index8700modules/18704facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage36%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: output Q/R images, zero padding and full memory frame from this actual
whole-function result; ordinary/scoped divmnu caller connection and the real
2-digit digits_len/digits_divmod branch. Continue through u256/full-multiply
wrappers and actual Taylor/header/main, then uniform target-step composition,
exact K, dominant slack review and final cleanup. Source-clock allowances omit
straight-line target work. Historical untracked WIPs and executable/fixed
premises stay untouched.


## Actual two-digit caller:606source ticks and complete padded arrays

The actual whole-function result now retains every source field except
locals/clock and its explicit workspace stores. Every word outside UN[0..m],
VN[0..1],Q[0..m-1],R[0..1] is preserved through normalization, the complete
quotient loop and final stores. The produced quotient prefix, genuine final
Q[m-1]=0 and both denormalized remainder words are retained in returned memory.

Earlier actual Q[m..15] and R[2..7] zeros now form complete physical16-word
quotient and8-word remainder images with32-bit digits. Their numbers are
ordinary U/D and U%D, with remainder<D. These zero-padding premises concern
the current input memory of divmnu; the earlier real digits_divmod clears
still must derive them in the caller connection.

The genuine six-scalar function signature and ordinary ignored-result call
are connected to the real body. Its all-outcome source allowance is40*m-34,
at most606for m≤16. An actual normal caller exposes its genuine callee return,
complete padded arrays, natural quotient/remainder, full outside-memory frame
and canonical retained caller metadata. Actual paid clocks remain variable;
no future successful child, exact worst-case funding or output oracle is
assumed. Both argument bindings and current physical buffers feed the same
actual callee execution.

Validation: current-two-digit-padded-caller-v4.log PASS1127jobs; all13new
printed facts have only permitted axioms. Index8700modules/18717facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage36%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: actual64-bit divisor digit conversion and digits_len=2 classification;
real digits_divmod Q/R clears, mm<n early return and reached divmnu call,
then physical digits_to_u256 reconstruction and the actual enclosing return.
The existing one-digit exact-clock contracts remain valid; the new two-digit
wrapper needs all-outcome allowances and actual normal-trace contracts because
its per-digit clock varies. Continue through u256/full-multiply wrappers,
Taylor/header/main, uniform target-step composition, exact K, dominant slack
review and cleanup. Source clocks omit target straight-line work. Historical
untracked WIPs and executable/fixed premises stay untouched.


## Actual64-bit divisor conversion, both scans and retained clear entries

The original u256_to_digits conversion of a64-bit divisor now has its exact
eight-word image. For divisor≥2^32 its high half is genuinely nonzero,
higher digits are zero, and the original digits_len returns2after exactly
seven scan ticks. The two-word image represents the original divisor exactly
and every actual converted digit is32-bit.

The unchanged converter call and both scoped digits_len calls now execute
into their real n/mm continuation with the full physical numerator and
divisor images retained. Its exact prefix charge is10+the actual numerator
scan count. All stopped/short-clock outcomes fit that allowance. A genuine
non-timeout enclosing execution derives the prefix's own funding and exact
continuation/restoration through the pinned evaluator clock theorem; no
future successful scan, scan value or paid clock is supplied as an oracle.

The same actual scanned image now supplies divmnu's physical two-digit
buffers whenever the current mm≥n branch applies. Clear-state preservation
retains both full input images, original formals, n=2 and the real trimmed
mm through separate Q/R zero stores. Their resulting Q[0..15]/R[0..7] zeros
and all six actual divmnu argument reads are checked. The branch/clear-loop
executions still must be composed with this actual scanned continuation;
these factory facts do not assume a future returned divmnu call.

Validation: current-two-digit-conversion-scans-v3.log PASS1127jobs;
all16new printed facts use only permitted axioms. Index8700modules/
18733facts; inventory8745/replacement closure0/fixed files unchanged.
Claim infinity; no global finite target K/full verifier success. Effort
estimate remains50%, plausible40–60%. Usage37%weekly/0resetcredits,
ordinary usage allowed. No new candidate paths; package stays65536entries.

Next: execute the original post-scan quotient clear, mm<n early-return
guard, remainder clear and reached divmnu caller. Reconstruct the actual
returned R quad via digits_to_u256, then connect the complete digits_divmod
body and u256 callers. Use the checked Length.scans_result_bound to couple
scan and division allowances when producing a tight full-width allowance.
Continue through full-multiply/Taylor/header/main, uniform target-step
composition, exact K, dominant slack review and cleanup. Source-clock
allowances omit target straight-line work. Historical untracked WIPs and
executable/fixed premises stay untouched.


## Actual two-digit wrapper clears, both branches and returned remainder

The original post-scan digits_divmod prefix now executes both real clears
and the actual mm<n guard. On the reached large branch, the real Q[0..15]
and R[0..7] zero stores supply divmnu's padded input requirements. Its actual
ignored-result call and physical digits_to_u256 reconstruction supply the
returned remainder quad, complete quotient image, natural U/D and U%D,
remainder<D, metadata and outside-memory preservation. Actual normal traces
derive their own clear funding and lexical restoration. The complete reached
post-scan large branch spends at most40*mm-9source ticks on every outcome.
Quotient cells above the original numerator width remain zero.

When the real numerator scan finds zero or one digit, the original guard
returns the physical numerator quad after quotient clearing, before either
remainder clearing or division. This branch spends exactly17ticks when
funded and at most17on every outcome. Any actual normal return derives its
own funding and returned quad. The actual short image proves U<D, so its
natural quotient is0and remainder isU; eight-word reconstruction equals the
full original numerator number. These are proved branch results rather than
assumptions of future successful calls.

Validation: current-two-digit-large-tail-v5.log PASS1127jobs; all16new
printed facts use only permitted axioms. Index8700modules/18749facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage37%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: combine both post-scan result contracts and their physical memory
frames with the already checked converter/two-scan prefix, using the actual
scan/trim coupling for the complete digits_divmod allowance. Connect original
workspace declarations and u256/full-multiply callers, then actual
Taylor/header/main, uniform target-step composition, exact K, dominant slack
review and cleanup. Source-clock allowances omit target straight-line work.
Historical untracked WIPs and executable/fixed premises stay untouched.


## Complete unchanged two-digit digits_divmod body and caller

Both actual post-scan branches now share one complete physical return
contract: full16-word quotient image,32-bit digits, natural U/D and U%D,
remainder<D, actual returned quad, zero quotient cells above the original
numerator width, retained nonlocal state and the exact outside-memory frame.
The earlier real clears supply their padding conditions, and the actual
converter/scans feed the same returned branch. Complete prefix and original
q/r/v lexical restorations are retained; no future successful child result,
future funding or fixed worst-case remaining clock is assumed.

The scan/trim relationship is used rather than adding independent maxima.
The complete unchanged digits_divmod body allowance is at most40*count+2:
322source ticks at8digits,642at16. Every ordinary call form adds1tick.
The genuine mixed scalar/quad ABI supplies the actual callee entry. A real
scoped callee return derives the full result and exact restored caller entry
at its actual variable remaining clock. At the original8-digit u256 width,
physical quotient reconstruction gives the full natural quotient.

Validation: current-two-digit-whole-body-v2.log PASS1127jobs; all18new
printed facts use only permitted axioms. Index8700modules/18767facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage37%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: connect these variable-clock actual-normal contracts to the original
u256_divmod/u256_div branches and physical numerator/quotient conversions.
Then combine one-/two-digit divisor paths at the actual Taylor entries,
finish actual counter/product/Taylor/header/main, compose uniform formal
target steps, evaluate exact K, review dominant slack and complete cleanup.
Source-clock allowances omit target straight-line work. Historical untracked
WIPs and executable/fixed premises stay untouched.


## Actual wide u256 division: physical input, both calls and complete return

The original u256_divmod wide branch now has a325source-tick all-outcome
allowance for a genuine two-digit64-bit divisor. Its actual numerator
conversion supplies the real eight-digit U image. The actual scoped
mixed scalar/quad digits_divmod call supplies its true padded quotient,
returned remainder and variable remaining clock. A second real scoped
call physically reads the quotient; the original eight-word return
contains precisely the natural A/D and A%D, with remainder<D. The entire
write frame through UN/VN/Q/R/V/U is retained, including the original
numerator-pointer scope restoration. No future helper return or worst-case
funding is assumed in the input requirements.

A shared inversion lemma derives funding, child return, shape checks and
the actual continuation from a genuine returned scoped call. The existing
read-only scalar fast-path proof was generalized to its actual D≤2^63
requirement; the one-digit theorem is now a wrapper around it. This avoids
duplicating the scalar proof and supports the later actual Taylor divisor
bound (below2^34). The executable and its branch tests are unchanged.

Validation: current-u256-two-digit-wide-v2.log PASS1127jobs; all7new
printed facts use only permitted axioms. Index8700modules/18774facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage37%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.

Next: combine the actual zero/magnitude/scalar tests and wide branch into
complete u256_divmod and u256_div contracts, including assigned callers.
Then connect one-/two-digit divisors to the actual Taylor loop, counter and
product bounds, finish header/main, compose uniform formal target steps,
evaluate exact K, review dominant slack and complete cleanup. Source-clock
allowances omit target straight-line work. Historical untracked WIPs and
executable/fixed premises stay untouched.


## Complete actual u256 division, assigned caller and main-input preservation

The actual positive-divisor guard, real u256_lt call, small-numerator return,
scalar fast path and two-digit wide branch are now connected into the complete
unchanged u256_divmod body. At genuine two-digit D≤2^63 entries its complete
all-outcome allowance is326source ticks. Its actual normal return supplies
the true quotient/remainder quads, natural A/D and A%D, remainder<D, retained
nonlocal state and the full physical memory frame through all workspace arrays.

The original u256_div wrapper receives that actual eight-word result and
extracts its quotient, with327body/328caller ticks. A real assigned call
derives its own positive call funding, exact next quotient binding and actual
remaining clock. It does not assume full worst-case funding. One shared
positive-word interface selects the existing one-digit or new two-digit
proof from the current divisor value, covering every0<D≤2^63 with the common
328caller allowance and a common UN/VN/Q/R/V/U outside-memory frame.

The actual assigned-call connection now preserves CurrentVerify.Data as well:
all decoded inputs, source globals/domain/code, protected physical memory,
heap and caller SI binding survive. The actual quotient and source allowance
are retained. Both the scalar fast-path bound and this shared interface cover
the real Taylor denominator range below2^34; deriving those actual counter/
product/denominator entries and the full loop remains the next work.

Validation: current-u256-word-caller-v4.log PASS1127jobs and
current-word-division-data-v5.log PASS1903jobs; all13new printed facts use
only permitted axioms. Index8700modules/18787facts; inventory8745/replacement
closure0/fixed files unchanged. Claim infinity; no global finite target K/full
verifier success. Effort estimate remains50%, plausible40–60%. Usage38%weekly/
0resetcredits, ordinary usage allowed. No new candidate paths; package stays
65536entries. Targeted builds are not full isolated submission verification.

Next: actual Taylor from-word/counter/product/overflow/divisor entries,
one continuing iteration and its true natural recurrence; connect the checked
positive-prefix bound of fewer than1280continuing terms to that actual loop.
Then finish Taylor/header/main, compose uniform formal target steps, evaluate
exact K, review dominant slack and complete cleanup. Source-clock allowances
omit target straight-line work. Historical untracked WIPs and executable/fixed
premises stay untouched.


## Literal Taylor program and actual denominator/division iteration suffix

The exact current taylor_exponential body is now checked against the fixed
Software AST, including original argument order, overflow trap, low-product
scope, from-word denominator, assigned division, counter increment, zero-test
assignment and final division. The new actual loop work lives in the existing
CounterLoopCost module, reusing the separate checked multiplication library;
no candidate paths or executable changes were introduced.

Actual one-word u256_mul callers now cost at most2ticks; a genuine assigned
normal call derives its own funding, exact128-bit product and read-only state.
If that product fits64bits, its real quad is exactly the scalar encoding used
by the division ABI. Actual u256_from_word scoped calls retain their real
one-tick boundary and lexical restoration on every outcome; their normal
contracts derive funding and the genuine reached continuation.

For each current index1..1280, the actual index*11684671 denominator fits one
word, is positive and at most14956378880 (hence below2^63). Its real assigned
multiplication supplies the precise physical division argument. The original
division/increment/zero suffix costs≤329source ticks; adding the denominator
multiplication costs≤331, and the actual from-word scoped prefix gives≤332.
All stopped and short-clock outcomes are covered. One actual completed suffix
derives the true natural quotient product/(index*11684671), next accumulator,
exact i+1counter and its actual zero flag, with full metadata, retained other
locals, workspace memory frame and original di scope restoration. No future
successful child, future paid clock or returned arithmetic value is assumed.
The index range is a current helper-entry condition; the whole actual loop
still must derive it from its same-execution recurrence/history.

Validation: current-taylor-denominator-prefix-v6.log PASS1137jobs; all20new
printed facts use only permitted axioms. Index8700modules/18807facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. Usage38%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries.
Targeted builds are not full isolated submission verification.

Next: actual full product and overflow guard, low-product declaration and
complete iteration; derive the actual positive-prefix recurrence and counter
range from the loop execution and apply the checked <1280positive-prefix
arithmetic bound. Then full Taylor/header/main, uniform formal target steps,
exact K, dominant slack review and cleanup. Source clocks omit target
straight-line work. Historical untracked WIPs and executable/fixed premises
stay untouched.


## Complete literal Taylor iteration and derived exact recurrence

The actual full-multiply product is now connected through the original
high-limb OR test, trap3and low-product declaration. A genuinely continuing
overflow guard derives that the full product fits256bits: trap_with cannot
fall through even if its FFI returns. The actual low limbs therefore represent
accumulator*numerator exactly. The trap and division routes cost their maximum,
332source ticks, including every stopped/insufficient-clock outcome.

The actual scoped u256_mul_full call derives its own17-tick funding and exact
scalar-right-operand product/caller state. The leading assigned u256_add call
has a read-only nonlocal frame and preserves all other caller locals; its
value is not assumed. The complete unchanged body iteration now has a350tick
all-outcome source allowance at a current index1..1280. Its actual normal
completion derives the true natural recurrence
next=accumulator*numerator/(index*11684671), the exact next accumulator tuple,
i+1counter and its real zero flag. Workspace/context metadata, protected memory
and unchanged loop constants survive the same execution and lexical scopes.
No future successful child, assumed low product or future funding is supplied.
The whole-loop history still must derive the current index range.

Validation: current-taylor-whole-iteration-v5.log PASS1145jobs; all10new
printed facts use only permitted axioms. Index8700modules/18817facts;
inventory8745/replacement closure0/fixed files unchanged. Claim infinity;
no global finite target K/full verifier success. Effort estimate remains50%,
plausible40–60%. No new candidate paths; package stays65536entries.
Targeted builds are not full isolated submission verification.

Next: instantiate the actual Taylor loop with its same-execution finite
history, derive active counters≤1280from the checked positive-prefix theorem,
prove actual successor/history and guard progress, then bound the whole loop.
Connect actual startup/final division/caller, finish header/main, uniform formal
target steps, exact K, dominant slack review and cleanup. Source clocks omit
target straight-line work. Historical untracked WIPs and executable/fixed
premises stay untouched.


## Actual Taylor whole-loop bound from its observed finite history

The literal original iteration cannot escape by break, continue or a caller
return; its real errors, traps and timeouts remain covered. The loop model now
records only already executed terms, their exact natural recurrence and the
current accumulator/counter/zero flag, fixed numerator/denominator, source
metadata and protected outside-workspace memory.

An active real guard proves the current term positive. The checked <1280
positive-prefix arithmetic then derives the actual active counter≤1280.
A real normal body extends that same history with its actual quotient, advances
the true i local without wrapping, preserves the model and decreases the rank.
The proof does not assume that the loop terminates or that future calls are
funded. Clock exhaustion and every aborted iteration are included.

The unchanged whole loop, at its actual initial i=1and true accumulator flag,
now has a449280source-tick all-outcome allowance:1280*(350body+1while tick).
Any genuine normal exit retains the same history/constants, complete source
metadata and protected memory, and its actual accumulator number is zero.
The initial scalar/tuple bindings and workspace remain current-entry facts;
the full function still must derive them through its original startup calls.

Validation: current-taylor-loop-history-v4.log PASS1145jobs; all12new printed
facts use only permitted axioms. Index8700modules/18829facts; inventory8745/
replacement closure0/fixed files unchanged. Claim infinity; no global finite
target K/full verifier success. Best overall effort estimate now55%, plausible
45–65%, relative to reference main; this is an effort estimate, not a measured
proof percentage. Usage38%weekly/0resetcredits, ordinary usage allowed.
No new candidate paths; package stays65536entries. Targeted builds are not
full isolated submission verification.

Next: original Taylor from-word startup, initial multiplication and actual
loop entry; final assigned division/return, full body and actual caller.
The loop model intentionally does not need the running sum's numerical value:
its final division can derive a valid quad from the actual successful ABI,
while failed reads/shape checks stop within the same allowance. Then connect
header/main, uniform formal target steps, exact K, dominant slack review and
cleanup. Source clocks omit target straight-line work. Historical untracked
WIPs and executable/fixed premises stay untouched.


## Complete unchanged Taylor body source bound:449602ticks

The original final assigned u256_div call is priced at316ticks with no
assumption about the running sum's value or shape. A genuine successful
current ABI lookup derives its actual four-word sum; failed reads or shape
checks stop within the same allowance. Its real normal return derives the
assigned quotient and full outside-workspace frame. The actual final return
contains that quotient quad and preserves all other source metadata.

The whole loop/final suffix now costs≤449596source ticks. The actual zero-test
scope supplies its true initial flag; literal out/i/zero declarations preserve
the genuine constants and install i=1. The initial assigned one-word product
of1and11684671derives its exact denominator accumulator and own2-tick boundary.
All three original from-word calls then feed that same real startup. The
complete unchanged taylor_exponential body at its actual factor1/denominator
11684671blob-price parameters costs≤449602source ticks, for every numerator
word, every incoming clock and every stopped outcome. No future successful
helper, whole-loop result or worst-case funding is an input premise.

The full-function returned-state/caller connection remains to be completed;
loop/final normal contracts already retain the actual value and protected
memory. Nothing follows yet about a uniform whole-program target-step K.

Validation: current-taylor-full-body-cost-v5.log PASS1148jobs; all17new printed
facts use only permitted axioms. Index8700modules/18846facts; inventory8745/
replacement closure0/fixed files unchanged. Claim infinity; no global finite
target K/full verifier success. Effort estimate55%, plausible45–65%, relative
to reference main. No new candidate paths; package stays65536entries.
Targeted builds are not full isolated submission verification.

Next: actual startup normal traces through every lexical scope, complete
Taylor normal return, real three-word caller and blob-price wrapper; then
header/main, uniform formal target steps, exact K, dominant slack review and
cleanup. Source clocks omit target straight-line work. Historical untracked
WIPs and executable/fixed premises stay untouched.

## Actual Taylor return, original caller and complete blob-price wrapper

The complete unchanged Taylor body now has a checked returned-state contract.
Its genuine startup, loop exit and final return supply the actual quotient
quad, restored lexical scopes, unchanged source metadata and every physical
memory cell outside the six division workspace buffers. These facts come
from the same execution, with no assumed future success or worst-case funding.

The original three-word Taylor ABI is connected to that body: factor 1,
arbitrary 64-bit numerator and denominator 11684671. Every ordinary call form
costs at most 449603 source ticks. A real returned child supplies the actual
caller continuation at its real remaining clock and retains the protected
memory frame.

The literal calculate_blob_gas_price wrapper now costs at most 449603 body /
449604 ordinary caller source ticks. Its actual scoped return carries the
same quad, metadata and outside-workspace memory back to the original caller.
Failed reads, short clocks and aborted child outcomes are covered by the cost.

Validation: current-taylor-caller-v3.log PASS 1148 jobs; all 14 new printed
facts use only permitted axioms. Index 8700 modules / 18860 facts; inventory
8745 / replacement closure 0 / fixed files unchanged. Claim infinity; no global
finite target K or full verifier success. Effort estimate 55%, plausible
45–65%, relative to reference main. No new candidate paths; package remains
65536 entries. Weekly usage 39%, no reset credits, ordinary usage allowed.
Targeted builds are not full isolated submission verification.

Next: connect the real blob-price result through calculate_excess_blob_gas
and the original header/main continuation. Then complete uniform formal target
steps, exact K, dominant slack review and cleanup. Source clocks still omit
straight-line target work. Historical untracked WIPs and fixed executable
premises remain untouched.

## Complete original excess-blob-gas body and caller cost

The unchanged calculate_excess_blob_gas helper now costs at most 449690 body
source ticks and 449691 ordinary caller ticks. This includes all four actual
parent-header declarations, its early zero return, the real blob-price call,
five arithmetic helper calls and the final nonzero scalar division. Its
post-price suffix costs at most 86 ticks; failed reads, ABI checks and short
clocks are covered throughout. The current workspace and installed code are
entry facts; no successful header load or future child return is assumed.

Scoped original callers have the same allowance plus their checked suffix.
An existing declaration rule and a new scoped-call rule price only entries
selected by the current execution, including failed reads/lookups. Cleanup
removes the unused quotient parameter from the shared WorkspaceResult frame;
returned values remain explicit equalities in the corresponding contracts.

Validation: current-excess-blob-caller-v4.log PASS 1149 jobs; all 10 new printed
facts use only permitted axioms. Index 8700 modules / 18870 facts; inventory
8745 / replacement closure 0 / fixed files unchanged. Claim infinity; no global
finite target K or full verifier success. Effort estimate remains 55%, plausible
45–65%, relative to reference main. No new candidate paths; package remains
65536 entries. Weekly usage 39%, no reset credits, ordinary usage allowed.
Targeted builds are not full isolated submission verification.

Next: actual excess-blob-gas normal-return memory frame and header caller;
then the remaining header/main continuation, uniform formal target steps,
exact K, dominant slack review and cleanup. Source clocks omit straight-line
target work. Historical untracked WIPs and fixed executable premises remain
untouched.

## Complete actual excess-blob-gas return and retained main inputs

The actual post-price arithmetic now preserves every memory cell and global,
including the real nonzero scalar division. Genuine returned price scopes
retain the blob-price result's outside-workspace frame through that arithmetic
and lexical restoration. The original early-return decision either finishes
without memory changes or reaches the same real price scope. All four actual
parent-header declarations then supply the complete helper normal-return frame.

The original helper's scoped caller receives unchanged metadata and protected
physical memory at the child's actual remaining clock. A shared caller-frame
rule adds only its own funded call tick. The current main-input record now
consumes any such whole-helper workspace frame and retains all decoded input,
heap, hash workspace and gas facts. SI is required only at the restored caller;
no SI binding is assumed in the helper's actual formal environment.

Validation: current-excess-blob-main-frame-v1.log PASS 1907 jobs, including
shared startup/input/hash dependencies and both changed proof modules. All 10
new printed facts use only permitted axioms. Index 8700 modules / 18880 facts;
inventory 8745 / replacement closure 0 / fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Effort estimate remains
55%, plausible 45–65%, relative to reference main. No new candidate paths;
package remains 65536 entries. Weekly usage 39%, no reset credits, ordinary
usage allowed. Targeted builds are not full isolated submission verification.

Next: bound the original calculate_base_fee_per_gas helper using the checked
word-divisor implementation. Its parent target is the actual 64-bit parent
gas limit shifted right once, hence below 2^63; zero divisors take their
real zero-result return path. Preserve its workspace frame and connect validate_header,
then finish the remaining main continuation, uniform formal target steps,
exact K, dominant slack review and cleanup. Source clocks omit straight-line
target work. Historical untracked WIPs and fixed executable premises remain
untouched.

## Complete unchanged base-fee calculation: 737 body source ticks

The shared word-divisor body/caller interface now covers zero, positive
one-digit and positive two-digit values through 2^63. Zero wide division
returns the real zero quotient; it does not trap. Genuine normal returns
supply their actual quotient quad, metadata and full outside-workspace frame.
Current scoped arguments derive their numerator shape only when the real ABI
lookup succeeds. No future child return or worst-case funding is supplied.

A common readonly-child rule preserves actual caller locals, memory and clock
for arithmetic and gas-limit checks. The original base-fee syntax is checked:
the actual parent-limit shift derives its target range, both real from-word
calls construct its denominator tuples, and the increasing/decreasing branches
cost at most 668/666 ticks. A selected increasing branch cannot fall through
into the decreasing branch. The real gas-limit call and early-return/raise
guards complete the all-outcome 737-body / 738-caller source allowance.
Malformed reads, shape checks and short clocks are included. Cleanup replaces
the duplicated excess-blob scalar-division frame with the existing shared
constant-divisor rule.

Validation: current-base-fee-body-v2.log PASS 1154 jobs; all 26 new printed
facts use only permitted axioms. Index 8700 modules / 18906 facts; inventory
8745 / replacement closure 0 / fixed files unchanged. Claim infinity; no global
finite target K or full verifier success. Effort estimate remains 55%, plausible
45–65%, relative to reference main. No new candidate paths; package remains
65536 entries. Weekly usage 39%, no reset credits, ordinary usage allowed.
Targeted builds are not full isolated submission verification.

Next: the actual base-fee normal-return workspace frame and original header
caller. The existing zero-divisor normal proof is reusable. Then finish
validate_header and the remaining main continuation, uniform formal target
steps, exact K, dominant slack review and cleanup. Source clocks omit
straight-line target work. Historical untracked WIPs and fixed executable
premises remain untouched.

## Complete actual base-fee normal return and original header caller

Normal memory frames now compose through actual calls, lexical restoration
and selected stopping branches. Readonly and word-division scopes obtain their
real child returns and continued caller executions from the same parent run.
Their spent-clock bounds compose without any assumed future funding or success.

Both original base-fee arithmetic branches now retain all metadata and memory
outside the six division workspace buffers. The actual from-word startup
supplies its exact target/eight tuples; the gas-limit check and early branches
retain the real scalar target. The complete unchanged helper has a checked
737-tick normal-return frame, including zero divisors and all lexical scopes.
The real original ABI identifies that body and reconstructs the header caller
at the child's actual remaining clock. Its source allowance remains 737 body /
738 ordinary caller ticks. The full validate_header connection is still open.

Validation: current-base-fee-full-normal-v1.log PASS 1155 jobs; all 23 new
printed facts use only permitted axioms. Index 8700 modules / 18929 facts;
inventory 8745 / replacement closure 0 / fixed files unchanged. Claim infinity;
no global finite target K or full verifier success. Effort estimate remains
55%, plausible 45–65%, relative to reference main. No new candidate paths;
package remains 65536 entries. Weekly usage 40%, no reset credits, ordinary
usage allowed. Targeted builds are not full isolated submission verification.

Next: connect the actual excess-blob and base-fee calls through unchanged
validate_header, retaining its real parent/payload header cells, bounded heap
and protected input; reuse checked header encoding/hashing and memeq. Then
finish the remaining main continuation, uniform formal target steps, exact K,
dominant slack review and cleanup. Source clocks omit straight-line target
work. Historical untracked WIPs and fixed executable premises remain untouched.

## Actual header-validation prefix: 450464 source ticks

The unchanged validate_header prefix through its nonce comparison now has an
all-outcome 450464-source-tick allowance: actual excess-blob and base-fee calls,
wide equality/zero checks, all intervening rejection guards and memeq8. Failed
reads, ABI/return-shape checks and short clocks are included. A generic fixed-
length memeq caller prices its actual ABI entry without pointer/mapping inputs.

Both real fee returns compose their existing division-workspace frames at the
child's actual remaining clock. A genuine reached action trace retains the
actual h/parent bindings and every cell outside that workspace before the
original heap_mark. The returning probe used to obtain this frame is justified
by that same action trace; no future child execution or funding is supplied.
The original literal body/prefix equality is checked. This stops before the
ommer and parent-header hashing section; the complete validate_header bound
and caller connection remain open.

The wider selected dependency build also repairs old bit-vector/modulo
simplifications, an already-closed proof goal and two arrow-token spacing
conflicts. Their theorem statements and the fixed executable are unchanged.

Validation: current-validate-header-prefix-v4.log PASS 3101 jobs; all 24 new
printed facts use only permitted axioms. Index 8700 modules / 18953 facts;
inventory 8745 / replacement closure 0 / fixed files unchanged. Incremental
policy PASS, 65536 package entries. Claim infinity; no global finite target K
or full verifier success. Effort estimate remains 55%, plausible 45–65%,
relative to reference main. No new candidate paths. Weekly usage 40%, no reset
credits, ordinary usage allowed. Targeted builds are not full isolated
submission verification.

Next: finish unchanged validate_header's actual temporary allocation and
ommer/parent-header hashing section, retaining the protected main input and
real heap. Then finish the remaining main continuation, uniform formal target
steps, exact K, dominant slack review and cleanup. Source clocks omit
straight-line target work. Historical untracked WIPs remain untouched.

## Actual empty-ommer hash check and parent-hash entry trace

The unchanged validate_header heap mark, temporary 64-byte allocation, marker
write, one-byte software Keccak call, memeq32 and rejecting release/BlockErr29
branch now cost at most 823 source ticks on every outcome. The hash's literal
length and actual ABI give its 690-tick caller allowance; arbitrary failed
temporary reads and malformed shapes are included. A reached rejecting guard
must have skipped its genuinely stopping failure branch.

The complete unchanged header prefix through that check now either stops
within 451287 source ticks or exposes the actual parent-header hashing suffix.
It retains the fee-entry workspace frame and the real mark/allocation/hash/
comparison action trace. The later physical memory frame is still to be
derived from those same actual actions; no future allocation or hash success
is an input to the runtime bound.

Validation: current-validate-header-ommer-v2.log PASS 3101 jobs; all 10 new
printed facts use only permitted axioms. Index 8700 modules / 18963 facts;
inventory 8745 / replacement closure 0 / fixed files unchanged. Incremental
policy PASS, 65536 package entries. Claim infinity; no global finite target K
or full verifier success. Effort estimate remains 55%, plausible 45–65%,
relative to reference main. No new candidate paths. Weekly usage 40%, no reset
credits, ordinary usage allowed. Targeted builds are not full isolated
submission verification.

Next: retain the actual temporary allocation/hash memory frame, then finish
the original parent-header hash and restored header caller. Continue the
remaining main path, uniform formal target steps, exact K, dominant slack
review and cleanup. Source clocks omit straight-line target work. Historical
untracked WIPs remain untouched.

## Actual temporary/hash frame at the parent-header hash entry

The real reached heap mark and 64-byte allocation now derive the allocation's
own room, exact saved mark/tmp bindings and live advanced heap. The marker
store, one-byte software hash, memeq32 and skipped rejection guard retain every
nonheap global and all earlier physical words above the fixed workspaces.
Their actual normal executions supply each intermediate state. Successful
allocation, hashing or comparison is not supplied as a future premise.

The complete original header prefix now either stops within 451287 source
ticks or reaches parent-header hashing with both real fee/temporary/hash
frames, retained h/parent bindings and the genuine suffix execution. The
incoming source hash environment and heap facts are retained through the
fee-workspace frame. Parent-header hashing and the restored whole caller
remain open; no uniform target-step bound follows yet.

Validation: current-validate-header-physical-entry-v1.log PASS 3101 jobs;
all 6 new printed facts use only permitted axioms. Index 8700 modules / 18969
facts; inventory 8745 / replacement closure 0 / fixed files unchanged.
Incremental policy PASS, 65536 package entries. Claim infinity; no global
finite target K or full verifier success. Effort estimate remains 55%,
plausible 45–65%, relative to reference main. No new candidate paths. Weekly
usage 40%, no reset credits, ordinary usage allowed. Targeted builds are not
full isolated submission verification.

Next: bound actual parent-header encoding/hashing and retain its real
restored heap/earlier-memory frame. Continue the remaining main path, uniform
formal target steps, exact K, dominant slack review and cleanup. Source clocks
omit straight-line target work. Historical untracked WIPs remain untouched.

## Complete unchanged memcpy bound for arbitrary requested lengths

Every real normal copy block must successfully write its first ordinary
memory cell. The exact fixed ordinary domain ends at 33806089704; its aligned
byte backing words obey the same exclusive bound. A current spatial invariant
retains dst, the real counter and a small overshoot allowance. Each genuine
continuing block advances a nonwrapping counter and strictly reduces its
spatial rank. The rank includes a possible final failing iteration.

All four unchanged memcpy loops, their alignment decision and actual lexical
counter declaration now have a uniform body allowance 43314052475 source ticks
for arbitrary requested lengths and source-pointer contents, including values
whose loop guards wrap near 2^64. The genuine three-word ordinary caller adds
one tick. Only the actual ordinary domain and typed destination binding are
needed; no source/destination mapping oracle, requested-length limit or future
successful copy is supplied. Existing length-based costs remain available for
known lengths. This fallback is for length facts not yet retained at the
parent-header encoding entry; it is not the final whole-program target K.

Validation: current-copy-domain-body-v1.log PASS 1175 jobs, then wider
current-copy-domain-header-replay-v1.log PASS 3101 jobs. All 16 new printed
facts use only permitted axioms. Index 8700 modules / 18985 facts; inventory
8745 / replacement closure 0 / fixed files unchanged. Incremental policy PASS,
65536 package entries. Claim infinity; no global finite target K or full
verifier success. Effort estimate remains 55%, plausible 45–65%, relative to
reference main. No new candidate paths. Weekly usage 41%, no reset credits,
ordinary usage allowed. Targeted builds are not full isolated verification.

Next: actual normal-copy length and earlier-memory frames, then the remaining
parent-header encoding/hash path and restored header caller. Continue the
remaining main path, uniform formal target steps, exact K, dominant slack
review and cleanup. Source clocks omit straight-line target work. Historical
untracked WIPs remain untouched.

## Actual arbitrary-length copy returns: length and earlier-memory frame

Every real normal copy block now preserves runtime metadata and each word
below an older aligned frontier. Its literal writes stay inside the finite
spatial span derived from the actual continuing block. Genuine normal loop
exits compose these frames. The original declaration and return retain their
real lexical restoration.

The actual final tail-loop zero test now derives the requested word length
at most ordinaryEnd-dst.toNat+31. This does not assume the length is small at
entry. The original three-word ABI/caller supplies the actual length word,
real child return, complete metadata and earlier-memory frame. No source or
destination mapping/success oracle is an entry premise. A missing explicit
result-memory import in the earlier fresh-copy frame helper is repaired;
its theorem statements and the executable are unchanged.

Validation: current-copy-domain-normal-v5.log PASS 1184 jobs; all 5 new
printed facts use only permitted axioms. Index 8700 modules / 18990 facts;
inventory 8745 / replacement closure 0 / fixed files unchanged. Incremental
policy PASS, 65536 package entries. Claim infinity; no global finite target K
or full verifier success. Effort estimate remains 55%, plausible 45–65%,
relative to reference main. No new candidate paths. Weekly usage 41%, no reset
credits, ordinary usage allowed. Targeted builds are not full isolated
submission verification.

Next: apply actual copy cost/normal contracts to parent-header byte writing,
encoding/hashing and the restored header caller. Keep sharper known-length
copy costs where the actual length is available. Continue the remaining main
path, uniform formal target steps, exact K, dominant slack review and cleanup.
Source clocks omit straight-line target work. Historical untracked WIPs
remain untouched.

## Actual byte writer: arbitrary pointers and requested lengths

The unchanged rlp_encode_bytes single-byte decision now has a checked
zero-tick all-outcome cost. A real fallthrough skipped the writing/returning
branch and restored its b local, leaving the exact source state. Its actual
header child costs at most 18 body ticks and supplies its real 1..9-byte scalar
return, metadata and resumed clock before the original memcpy/return suffix.

The complete byte-writer body now costs at most 43314052495 source ticks for
arbitrary requested lengths, with +1 for ignored, assigned and tail callers.
Known lengths retain the smaller CopyAny.price(length)+20 body / +21 caller
allowance. Both rules use the proved original copy bodies at the actual ABI
entry. No source/destination ownership, mapped-pointer oracle or future
successful read/header/copy/funding is supplied. The generic composition's
copy callback is explicitly discharged by these checked bodies.

Validation: current-byte-writer-any-caller-v1.log PASS 1197 jobs; all 8 new
printed facts use only permitted axioms. Index 8700 modules / 18998 facts;
inventory 8745 / replacement closure 0 / fixed files unchanged. Incremental
policy PASS, 65536 package entries. Claim infinity; no global finite target K
or full verifier success. Effort estimate remains 55%, plausible 45–65%,
relative to reference main. No new candidate paths. Weekly usage 41%, no reset
credits, ordinary usage allowed. Targeted builds are not full isolated
submission verification.

Next: the same writer's genuine encoded-length and earlier-memory frame.
Use the parent encoder's fixed field sequence with the smaller costs for
fixed byte lengths and the domain fallback for its one extra-data length.
This can bound arbitrary actual parent-header reads without assuming a parent
record image discarded by the earlier main trace. Normal copies derive small
lengths before later hashing; protect memory below the real output buffer.
Then finish parent encoding/hashing, the restored header caller, remaining
main path, uniform formal target steps, exact K, dominant slack review and
cleanup. Source clocks omit straight-line target work. Historical untracked
WIPs remain untouched. Review the coarse final-copy tail allowance when
reviewing dominant slack; the actual byte-loop exit can give a shorter tail.

## Actual byte-writer return and assigned caller without input ownership

A real returning single-byte branch supplies its actual scalar one and
nine-byte write frame. Every real fallthrough leaves the exact original
source state. On the general path, the genuine header return gives length
1..9; the actual normal copy then bounds its requested length. The real
add/return derives a positive encoded natural at most count.toNat+9 and at
most ordinaryEnd+40, together with the exact returned word and full metadata.

The writer retains every word below an earlier aligned output frontier. Its
current destination's nine-byte header extent must not wrap; the encoder's
real cursor still has to discharge that numerical condition. No source or
destination ownership/mapping oracle, later success or worst-case funding is
supplied. The assigned caller derives one actual encoded word, retains all
other caller locals and protects the complete earlier-memory interval.

Validation: current-byte-writer-any-frame-caller-v2.log PASS 1197 jobs; all 4
new printed facts use only permitted axioms. Index 8700 modules / 19002 facts;
inventory 8745 / replacement closure 0 / fixed files unchanged. Incremental
policy PASS, 65536 package entries. Claim infinity; no global finite target K
or full verifier success. Effort estimate remains 55%, plausible 45–65%,
relative to reference main. No new candidate paths. Weekly usage 41%, no reset
credits, ordinary usage allowed. Targeted builds are not full isolated
submission verification.

Next: price dynamic byte-field arguments on every outcome, then the fixed
parent-header encoding sequence using its real allocated output cursor and
these weaker writer contracts. The actual encode_header prepends its list
header in the reserved prefix; it does not compact with a final memcpy.
Derive its returned span and old-input frame before the hash. Then finish
the restored header caller, remaining main path, uniform formal target steps,
exact K, dominant slack review and cleanup. Source clocks omit straight-line
target work. Historical untracked WIPs remain untouched.

## Dynamic original byte-field calls

The original byte writer now prices arbitrary actual three-expression field
arguments, including failed reads and invalid argument shapes. Successful
lookup derives all three scalar words and their real callee bindings. The
unknown-length call costs at most43314052496source ticks; a literal fixed
length n costs at most CopyAny.price n+21. No input/output ownership or
future successful run is supplied. These are source clocks, not final target
steps.

Validation: current-byte-writer-dynamic-header-replay-v1.log PASS3102jobs,
including TransactionData and its real header-entry callers; all3new printed
facts use permitted axioms. Index8700modules/19005facts; inventory8745,
replacement closure0, fixed files unchanged. Incremental policy PASS with
65536package entries. Claim infinity; no global finite target K or full
verifier success. Effort estimate55%, plausible45–65%, relative to reference
main. No new candidate paths. Weekly usage42%, no reset credits, ordinary
usage allowed. Historical untracked WIPs remain untouched.

Next: derive the wide writer's cost and actual return/frame without output
ownership, using only its own real fresh scratch allocation. Then compose
the fixed original parent-header encoding sequence, returned span and old
input frame, actual parent hash, restored header caller and remaining main
path; transfer to uniform formal target steps, exact K, review dominant
slack and finish cleanup. The original executable stays unchanged.

## Current wide writer without output ownership

The original wide writer now costs at most133source body ticks on every
outcome, without a destination arena premise. An exhausted actual allocator
stops within3ticks. A successful32byte scratch request supplies the owned
minimum writer, whose actual return has length≤32. The weaker byte contract
then prices every real output outcome, including failed mapping/read/store.

Actual normal returns derive1..41encoded bytes, full metadata with the
original saved heap restored, and every word below the aligned output/
scratch frontier. The minimum writer's normal length and scratch-only frame
are recovered at the actual clock; no future success, output ownership or
worst-case funding is supplied. The only caller numerical condition is the
nonwrapping9byte header extent, plus the real heap geometry/frontier; the
parent encoder must derive these from its actual cursor and allocation.

Validation: current-wide-writer-any-frame-v3.log PASS1236jobs; all5new printed
facts use only permitted axioms. Index8700modules/19010facts; inventory8745,
replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K or full
verifier success. Effort estimate55%, plausible45–65%, relative to reference
main. No new candidate paths. Weekly usage42%, no reset credits, ordinary
usage allowed. Historical untracked WIPs remain untouched.

Next: connect the current scalar/wide dynamic field callers, then compose
the original fixed parent-header encoder and its real normal output span/
protected input frame. Continue actual parent hash, restored header caller,
remaining main path, uniform formal target steps, exact K, dominant slack
review and cleanup. Source clocks omit straight-line target work. The
original executable stays unchanged.

## Actual scalar and wide field callers

Successful dynamic2expression evaluation now derives both real reads; the
original scalar/four-word ABI derives the actual output pointer and4limbs.
The scalar and wide field callers cover failed reads/ABI checks and all
callee outcomes, with19and134source ticks respectively. The wide caller
uses the real bounded heap and requires no output arena.

Genuine assigned calls derive their1..9or1..41encoded word, exact full
metadata/restored heap, all memory below the aligned output/scratch frontier
and every other caller binding. Numerical header nonwrap/frontier conditions
remain actual encoder obligations. Shared argument/shape facts live in the
existing scalar lookup module; no candidate paths were added.

Validation: current-scalar-wide-field-callers-v2.log PASS1236jobs; all8new
printed facts use permitted axioms. Index8700modules/19018facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to reference main. Weekly
usage42%, no reset credits, ordinary usage allowed. Historical WIPs untouched.

Next: compose the original fixed parent-header fields with the weaker
writer contracts, preserving the actual cursor, real heap and earlier input
memory without a parent-record image premise. Derive the returned span,
finish actual parent hashing/restored header caller and remaining main;
then uniform formal target steps, exact K, dominant slack review and cleanup.
Source ticks omit straight-line target work; executable unchanged.

## Field sequence with actual reads and no parent-record image

Every original header field now has an all-outcome cost and genuine normal
return/frame contract without supplied decoded parent-header values. Fixed
byte lengths retain their small allowances; only the extra-data field uses
the finite-domain fallback. Actual normal calls derive their encoded word,
full metadata/restored heap and all earlier memory. The real pointer advance
derives the next natural cursor and preserves other caller bindings.

The unchanged fields syntax now composes those contracts only at genuinely
reached normal states. An induction derives the bounded final cursor and
protected input prefix when a real returning continuation is reached; failed
reads, ABI checks, stores and allocations are already charged. The encoder
must still derive each numerical cursor/frontier and literal-size condition.
No future successful execution or parent-record image is assumed.

Validation: current-header-fields-no-image-v1.log PASS1246jobs; all7new printed
facts use permitted axioms. Index8700modules/19025facts; inventory8745,
replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to reference main. Weekly
usage42%, no reset credits, ordinary usage allowed. No new candidate paths;
historical untracked WIPs untouched.

Next: connect the actual encoder's first scoped byte call, optional branch
and final list header to this weaker sequence contract; derive its returned
span and protected input frame. Then actual parent hash, restored header
caller, remaining main path, uniform formal target steps, exact K, dominant
slack review and cleanup. Source clocks omit straight-line target work.
The original executable stays unchanged.
