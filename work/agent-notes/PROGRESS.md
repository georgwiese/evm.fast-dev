# Current proof progress — 2026-10-28

Active plan: [bound.md](../../bound.md). Reference main:
`f892870c8682517186860842a3ff5f0dea1aa3eb`; actual Software AST.
**No global finite target K yet**; claim infinity; no complete verifier run.

## Complete current byte-list/vector hash bodies and callers now check

BytesListCost composes the actual mark, packing, real returned tuple, Merkle,
release and length mix. Body/caller sourcecost≤packPrice(n)+88*ceil(n/32)+4*budget+
99/100. Actual chunks and list limit must fit2^budget, budget<58. BytesVectorCost
checks both its literal≤32byte early-return branch and long packed-Merkle phase;
body/caller sourcecost≤packPrice(n)+88*ceil(n/32)+4*budget+52/53. All actual
non-timeout observations include failed reads/stores/allocations and traps.

A small shared BytesCallCost ABI selects exactly the current vector/list Software
entry and supplies p/n/out plus the list limit to that same callee. These bounds
require no heap pointer/room, mapped input/output, accelerator/global workspace,
successful hashing or future funding. Source ticks still omit straight-line
target work. Global finite K and full root-hash composition remain open.

Validation: current-byte-hash-callers-v2.log PASS1608jobs/permitted printed
axioms;8GiBguard/twoslots/cachefalse. Index8051modules/16100facts; Solver8090;
replacement closure0/fixed files unchanged; incremental policy PASS64859entries/
2482482437bytes. Account24%weekly/0resetcredits. Claim infinity; no full verification.
Next: current progressive hashing, list/container composition and physical-memory
frames for complete payload/request-root hashing.

## Actual byte packing cost and returned chunk count now check

PackBytesProgram now uses the actual Software entry and minimal code/scalar/arena
imports, reducing its Solver import closure593→27 with all other sources held
current. A generic n+31<2^64 chunk-read theorem replaces the old128MiB restriction;
the historical API remains a projection. Its two-word ABI moved to a small shared
module; historical old runtime code imports it rather than redefining the proof.

PackBytesCost proves every body outcome costs at most copyPrice(n)+zeroPrice(pad)+4,
where actual padding≤31. This is≤copyPrice(n)+41. No input mapping, heap pointer,
room, future success or clock lower bound is supplied. PackBytesReturn inverts the
same real declarations, checked scalar allocation, copy/zero continuations and
literal return to derive the actual tuple(buffer,ceil(n/32)). Its ordinary caller
and scoped continuation contracts use that exact returned tuple, on all outcomes
or the same observed non-timeout parent outcome as appropriate.

A shared scalar-scope non-timeout composition also checks without the old RLP
import. ClockCostTerminatingScoped now directly imports its continuation-state
interface instead of relying on an accidental transitive import.

Validation: current-pack-complete-cost-v2.log PASS1603jobs/permitted printed
axioms;8GiBguard/twoslots/cachefalse. Index8048modules/16082facts; account24%weekly/
0resetcredits. No global finite target K; claim infinity; no full verification.
Next: byte-list/vector composition using actual packed counts, then progressive
hashing and complete root-hash ownership/resource composition.

## Complete current software Merkle body and caller costs now check

MerkleBufferCost checks the actual copy/clear/cur-declaration prefix and retains
its six caller locals through the same actual normal calls. Complete buffer fill,
dense tree, extension/output/release work costs≤44*capacity+2*(target-depth)+42.
MerkleAllocationCost includes both real heap_mark and persistent allocation,
including their failed/partial paths, reaching≤44*2^depth+2*(target-depth)+45.
These current-state theorems require no heap pointer, room, mapped arena, workspace,
successful hash or incoming-clock lower bound. ScalarScope's continuation contract
is invoked only after an actual checked scalar return reinstalls caller locals.

MerkleBodyCost combines the actual current depth prefix, least-covering capacity,
empty early return and complete nonempty phase. Every actual non-timeout body
outcome costs≤88*n+4*budget+48 when actual n,limit≤2^budget and budget<58. The real
four-word caller costs≤88*n+4*budget+49, including errors/traps/FFI. The surrounding
observation supplies non-timeout; successful Merkle return is not assumed. Large
straight-line target work and complete request-root composition remain open.

Cleanup extracts the shared scalar-shape lemma from serialization into a minimal
module, dropping ClockCostScopeLocals' obsolete RLP dependency. It also moves the
unchanged four-word Merkle ABI proof into a small shared environment module; the
historical old cost module imports that ABI rather than redefining it. That old
accelerator-dependent runtime proof remains historical/unselected.

Validation: current-merkle-complete-cost-v1.log PASS1596jobs/permitted printed
axioms;8GiBguard/twoslots/cachefalse. Index8043modules/16068facts; account24%weekly/
0resetcredits. No global finite target K; claim infinity; no full verification.
Next: actual pack_bytes and byte/progressive hash composition with decoded bounds.

## Current Merkle dense and extension suffix costs now check

CounterLoopCost now shares one checked rank/progress proof between unsigned and
nonnegative signed comparisons; the previous unsigned API remains. Actual Software
Merkle pair loops instantiate the signed case. Each dense/extension iteration
costs at most2source ticks, including failed SHA argument/memory operations and
partial executions. The halving outer loop telescopes to3*(capacity-1), avoiding
an extra logarithmic multiplier. No input/output mapping, workspace, future
success or incoming-clock lower bound is required for these loop cost theorems.

FixedMemoryCost prices actual literal-length zero/copy calls including failed
pointer expressions and malformed arguments. FixedHashCost composes real length
mixing at46body/47caller and u64root at53body/54caller source ticks. MerkleSuffixCost
checks actual selected suffix syntax, prices output copy/release at43 and composes
whole dense/extension/output work≤3*(cur-1)+2*(target-depth)+43 on all outcomes.
These source tick counts still omit large straight-line target work.

MerkleProgram now imports current code instead of the obsolete SHA accelerator
closure and uses the checked actual Software declaration entry. UnsignedMax uses
Software, CeilLog2Call explicitly imports its unary ABI lemma, and the complete
current depth-prefix trace rechecks. Actual buffer allocation/fill and complete
request-hash composition remain open; ordinary-domain arena extent must never be
substituted for the smaller persistent allocator limit.

Validation: current-merkle-suffix-cost-v1.log PASS1588jobs/permitted printed
axioms;8GiBguard/twoslots/cachefalse. Index8037modules/16050facts; Solver8076;
replacement closure0/fixed files unchanged. Account24%weekly/0resetcredits.
No global finite target K; claim infinity; no full verification.

## Actual hash callee data and software SHA memory frame now check

CurrentHash's shared effects bridge reuses8startup helper proofs for all five
retained globals: scratch/frame cursors and offsets/length-chunk/zero-hash pointers.
The complete31-helper body/caller closure now preserves all five on every outcome.
Workspace.after_body/after_call carry the real installed code/domain/endian and
workspace extents, without successful future hashes or memory-read premises.

Invocation identifies the actual two-word request-hash ABI and callee. From the
same RootEntry.Ready it carries full payload image, SI0/8/16/24/32physical cells,
mapped/aligned SI/root arenas and real heap/root/array separation. A non-timeout
observation of the enclosing unchanged main suffix derives funding and the same
callee's non-timeout execution; no unrelated existential invocation is substituted.

ByteOutputFrame has a compact checked syntax recognizer and structural all-outcome
memory-frame theorem for stable-local byte-output bodies. Sha256Memory checks the
expanded current Software.sha256_pair: only its32output bytes can change memory.
Its actual normal caller inherits that frame through the same ABI. No SHA global
state, accelerator buffer, input mapping or successful-read assumption is needed.
This replaces the old accelerator-dependent frame for current hash composition;
large straight-line target work remains open.

Validation: current-hash-physical-entry-v3.log PASS1540jobs/permitted printed
axioms;8GiBguard/twoslots/cachefalse. Index8032modules/16023facts. No global finite
target K; claim infinity, no full verification. Account23%weekly/0resetcredits.
Next: compose current byte/hash helper and loop costs with actual resource bounds.

## Real SSZ workspaces now reach the whole-source hash caller

A single three-key OffsetsFrame proof now preserves offsets, length-chunk and
zero-hash globals through the43actual decoder/startup helpers. The original
first three startup calls derive all three literal pointers; main's later startup,
caught decoder and root allocation retain them. WorkspaceEntry attaches installed
code/domain/endian, real mapped/aligned32-byte chunk and2048-byte zero-table extents
to the same reached caller. Both extents end before the same actual copied input.
No accelerator, successful future hash, room or funding assumption is supplied.

RootCut now accepts an optional reached-state property with checked refinements,
so strengthening physical data reuses its actual observation/stopped-path split.
The default interface remains available. The generic workspace proof avoids two
more copies of the large generated offsets proof.

Validation: current-hash-workspace-entry-v2.log PASS1510jobs/permitted printed
axioms;8GiBguard/twoslots/cachefalse. Index8027modules/16001facts; Solver8066;
replacement closure0/fixed files unchanged. Account23%weekly/0resetcredits.
No global finite target K, claim infinity; no full verification. Next: retain
all five arena/workspace globals through the actual hash closure and join its ABI.

## Actual root allocation and whole-source hash-entry split now check

RootEntry cuts the unchanged main immediately after its actual32-byte root
allocation. It derives real room/alignment, source heap cursor, target post-heap,
SI/root caller locals, actual two-argument hash ABI and output-after-decoded-record
separation. The complete ReturnedImage moves with a proved memory/heap interval;
the selected decoder Snapshot stays at its original state, since allocation
actually changes globals. Both real arenas/domain/code/endian survive.

RootCut proves all-outcome root-prefix sourcecost≤2 and arena preservation. Its
actual execution split reaches RootEntry.Ready or retains the original stopped
root-allocation prefix. It refines MainDecodedState and whole source observations,
keeping earlier stops, final result, source clocks and FFI event equality. No
normal-hash result or future clock/room hypothesis is introduced. Global runtime
and target work remain open. Next: SSZ hash workspace globals and current hash
loop/memory-frame composition.

Validation: current-hash-root-cut-v1.log PASS1508jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. Index8025modules/15986facts; Solver8064; replacement
closure0/fixed files unchanged; incremental policy PASS64835entries/2482330954bytes.
Account22%weekly/0resetcredits. Claim infinity; no full verification.

## Current supporting hash helpers now have checked all-outcome source costs

Copy32Program/loop-shape proofs now refer to actual Software.memcpy; its code entry
uses minimal OriginalEntry/OriginalCode imports. Current zero-byte shapes and log2
syntax/entries also use Software. CounterStrideLoop no longer relies on an imported
by_contra tactic; Nat.le_trans and a direct ZeroLoopTail import make the relevant
clock/counter proofs independent of the removed umbrella imports. The unrelated
legacy BufferGlobals/obsolete accelerator closure remains outside this batch.

CurrentHash.MemoryCost checks real copy/zero entries and provides tail/ignored/
local-result call costs price(length)+1, where price=length/32+length/8+length/8+
length. Only actual ABI values and length+32<2^64 are required; pointers may be
unaligned/unmapped and stores may fail. StraightCost checks heap_mark/max/st_le32
straight syntax and caller≤1; actual st_le64 has two32-bit calls, body≤2/caller≤3.
AllocatorCost checks actual persistent allocation caller≤2 without cursor/room
premises, and heap_release caller≤1. Log2Cost uses actual sufficient-fuel execution
or the smaller incoming-clock budget to prove all outcomes body≤depth/caller≤depth+1
for actual n≤2^depth, depth<64. No future return or funding premise.

Validation: current-hash-leaf-cost-v1.log PASS1179jobs/permitted axioms; actual hash
prefix included. Index8023modules/15976facts; Solver8062; replacement closure0/fixed
files unchanged; incremental policy PASS64831entries/2482279722bytes.8GiBguard/
twoslots/cachefalse; account22%weekly/0resetcredits. No global finite target K,
no whole verifier run. Next: actual root allocation/data/workspace entry and
composed current hash loops/memory frames/straight-line target weights.

## Software SHA pair: compact checked syntax and all-outcome source pricing

StraightBody.accepts recognizes fixed syntax without calls, loops, source ticks
or global writes. Its structural soundness theorem proves both QuietClock and
arbitrary-key GlobalEffects on every actual outcome, including memory/expression
errors. Recursive proof is kernel checked; no native evaluation/axiom or successful
read premise. A byte-store clock lemma covers the actual final digest stores.

CurrentHash.Sha256Pair now reduces the actual Software declaration through its
current Code entry and checks that syntax. It preserves all globals, retains the
old arena-preserves interface, spends0body source ticks and at most1caller tick
for real tail/ignored/local-result calls on all outcomes. The helper shrinks
1022→50lines. This does not price the expanded straight-line target instructions
or prove its output-memory frame. The generator now retains this compact module;
cleanup manifest records previous/current bytes and successful selected closure.

Validation: current-sha-pair-clock-v4.log PASS378jobs, including actual hash-prefix
arena/observation closure; permitted printed axioms. Earlier full payload selected
closure remains current-full-payload-image-v2.log PASS1480jobs. Index8019modules/
15961facts; Solver8058; replacement closure0/fixed files unchanged; incremental
policy PASS64827entries/2482266477bytes.8GiBguard/twoslots/cachefalse; disk60%;
account22%weekly/0resetcredits. No global target K; claim infinity; no full verification.

## Complete payload hash data now reaches main's selected decoder post-state

RemainingImage proves every one of the actual eleven final literal field values,
with memory/return frames and concrete withdrawal/balance projections. ReturnedImage
combines that data with the real transaction/prefix image, passing four-offset
validation, original payload length and withdrawal quotient/remainder facts.
PayloadGasReturned constructs it from the same actual suffix and complete return.
PayloadCallerReturn retains it once; existing transaction-only APIs project it.

RequestTransactions and DecodedTransactions now carry the stronger ReturnedImage
through the exact same stores, request allocation and protected witness interval.
Their previous transaction APIs remain projections. MainDecodedPayload identifies
the complete image with the same actual RootRun, main si binding and snapshot;
array-end≤requestRecord is retained. The root hasher's physical payload-data gap
is closed. No hash runtime/global target bound is claimed.

Next: carry actual workspace/root allocation into hashing and migrate current
software sha256_pair. It has no helper calls and expanded straight-line software
operations; old ShaPair.Workspace requires obsolete sha_accel facts. Older hash
Description.Layout pins budget≤134217728, below the current checked shared resource
ceiling251655056, so syntax/entry/budget assumptions must be checked before reuse.
Remaining witness SI fields should be proved at the actual caller that needs them.

Validation: current-full-payload-image-v2.log PASS1480jobs/permitted axioms;
8GiBguard/twoslots/cachefalse. Index8018modules/15954facts; Solver8057; replacement
closure0/fixed files unchanged; incremental policy PASS64826entries/2482309152bytes.
Account21%weekly/0resetcredits. Claim infinity; no full verification.

## Early payload hash fields now survive with the complete transaction image

PayloadCut.input_frame also retains the actual raw-pointer cell selected by its
real PLbinding. PayloadWorkspace/Validated/Extra carry that cell, including the
four low SSZ workspace writes. TransactionEntry now uses the checked exact two
extra-data stores instead of separately observing and reconstructing both stores;
its real prepared state supplies Payload.PrefixImage(raw0/extra16/length24/≤32).

VarListData, TransactionReturn and WithdrawalReturn preserve that prefix through
the actual list call and PL32/40stores. PrefixImage.store_after/fields_after prove
that transaction and final payload writes cannot change it. TransactionImage now
retains the prefix; existing interval/return/request/witness transports carry it
to the same actual main state. Remaining hash inputs include the withdrawal and
balance fields; no global runtime K is claimed.

Validation: current-payload-prefix-image-v3.log PASS1477jobs/permitted axioms;
8GiBguard/twoslots/cachefalse. Index8015modules/15940facts; Solver8054; replacement
closure0/fixed files unchanged; incremental policy PASS64823entries/2482293970bytes.
Account21%weekly/0resetcredits. Claim infinity; no full verification.

## Complete transaction records now survive to actual main, with tighter resource bounds

VarListData derives the actual allocation end for its complete returned array;
TransactionReturn and WithdrawalReturn retain it. PayloadFieldsFrame proves
literal field writes preserve all other cells and earlier transaction arrays.
Payload.TransactionImage packages actual records, PL32/40pointer/count, canonical
slice positions, containment and real heap extent. Its after_remaining/of_frame
lemmas carry the whole image through the eleven final payload stores, complete
return and actual PayloadCallerReturn. No decoder program change.

RequestsAllocation now retains the actual incoming caller heap pointer, propagated
through RequestsCountsEntry/RequestsReturned. RequestMetadataCells.stores factors
the genuine three-store state so metadata and transaction proofs share it.
RequestTransactions transports the same actual image through SI0 and hash metadata.
DecodedTransactions derives transaction-array-end≤rq from the real cursor, retains
it through the request decoder and SI32store, then uses the shared protected witness
frame. MainDecodedTransactions joins it to the same actual main continuation.

Joint physical room derives encodedLength+16*txCount≤251655056, txCount≤12582752,
and total transaction bytes≤251655056. These are resource bounds for a normally
returned decoder; earlier stopped alternatives remain in the main cuts. They are
not a global runtime bound. Remaining work includes witness/nontransaction payload
fields, actual hash/caller costs, covered scratch consequences and target transport.

Validation: current-main-decoded-transactions-v1.log PASS1473jobs/permitted axioms;
8GiBguard/twoslots/cachefalse. Index8012modules/15935facts; Solver8051; replacement
closure0/fixed files unchanged; incremental policy PASS64820entries/2482282734bytes.
Account21%weekly/0resetcredits. Claim infinity; no full verification.

## Shared witness frame and actual main request-hash argument loads

WitnessProtected describes the earlier SI/payload/request memory interval,
excluding only six actual witness output fields. WitnessPrefixFrame composes
real workspace/allocation/caller frames across all three list returns and the
same selected snapshot. It also directly retains SI32=requestRecord. This
replaces repeated field-specific geometry in DecodedPayloadPointer. Its source
shrinks185→117lines while preserving public helper statements; request metadata
proofs now live in a smaller independently importable RequestMetadataCells.

RequestMetadataCells proves the actual SI0/8/16/24 stores and exact versioned-hash
count. RequestCallerReturn.earlier_memory generalizes its protected earlier-cell
frame. DecodedRequestFields carries SI8/16/24/32 to the actual snapshot. The
MainDecodedRequest.si_load helper checks real ordinary-domain mapping; actual
main decoder executions derive the four genuine hasher argument loads. Remaining
witness/chain fields, full payload transaction lifetime, hash runtime and target
composition remain open. No finite global K or full verification.

Validation: current-main-decoded-request-v1.log PASS1463jobs/permitted axioms;
8GiBguard/twoslots/cachefalse. Index8005modules/15920facts; Solver8044; replacement
closure0/fixed files unchanged; incremental policy PASS64813entries/2482253694bytes.
Account20%weekly/0resetcredits. Program and infinity claim unchanged.

## Actual main loads now reach the bounded physical payload gas

Request validation/allocation/counts retain their exact outside-memory frames;
witness validation retains the corresponding24-byte workspace frame. Witness
prefix/readonly-load models expose their exact prepared state. The final header
result retains its allocation lower bound and memory below that array except
the two genuine SI72/80stores. HashCountReturn retains its actual count-call
memory frame. These are facts from existing executions, not extra hypotheses.

CallerSiBase centralizes actual96-byte record field separation and genuine
later scalar-store preservation. DecodedPayloadPointer follows the actual si+0
store through all metadata/request/witness stages and the same rooted Snapshot.
MainDecodedGas proves both the actual payload-pointer load and nested pl+88gas
load at main's continuing decoder return, including real ordinary-domain mapping
and gas≤200000000. Other SI fields and full payload transaction records remain
open, as do reachable runtime and target composition. Program/claim unchanged.

Validation: current-main-decoded-gas-v1.log PASS1459jobs; all printed axioms
permitted,8GiBguard/twoslots/cachefalse. Index8001modules/15900facts; Solver8040;
replacement closure0/fixed files unchanged. Incremental policy PASS64809entries/
2482231548bytes. No full verification. Account20%weekly/0resetcredits.

## A selected stateless run now supplies physical facts at actual main continuation

DecoderOrigin fixes a particular entry/post/pointer/word; its Frame preserves the
same original nonlocal state, value and clock. SeparatedInput.EntryReturn factors
the original run prerequisites; RootRun is indexed by that exact origin, while
StatelessRun remains an existential compatibility statement. stateless_run_root
selects the actual stateless callee and relates its post-state to the same host
call target. Root indices are implicit on phase models/endpoints, threaded from
RecordEntry through PayloadEntry.Invocation and the existing actual return chain.
Generic Context/byte-list/math helpers remain origin-independent. The old
separated wrappers now take the selected RootRun; no arbitrary existential
intermediate state is identified with a main endpoint.

StatelessReturned.rooted transports the final witness snapshot to that same
original stateless post-state; physical projects bounded physical gas, copied
input, bounded heap and all3record arrays/headercount≤256. MainDecodedRoot selects
the true run from an actual continuing main decoder action trace. MainDecodedState
joins the physical snapshot to main's actual si binding/afterDecoder state and
complete source observation; all earlier stopped alternatives and original FFI
observations remain. This closes the witness/gas snapshot's decoder/main endpoint
selection gap. Concrete SI field images and complete payload transaction-record
lifetime still need materialization for actual hash/attempt arguments, followed
by reachable runtime and target-step composition. No global finite K.

Validation: current-main-decoded-state-v1.log PASS1456jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. The earlier rooted model closure passed1453jobs and
selected stateless/root projections1455jobs. No full verification. Account19%
weekly/0resetcredits/ordinaryallowed.

## Shared invocation descriptor keeps the selected caller explicit

PayloadEntry.Invocation factors the existing caller/callee/parent-post/ownership/
ABI facts from the end of Result. PayloadCallerReturn and PayloadCallReturned
retain that descriptor indexed by their same actual caller, callee and parent
post rather than unrelated existential invocation data. This is proof-interface
cleanup; no guest/semantics change. Validation: current-payload-invocation-v2.log
PASS1452jobs/permitted printed axioms,8GiBguard/twoslots/cachefalse.

Next origin-index step: stateless post-state selection must remain explicit
through the stage chain. Plan is a DecoderOrigin(entry/post/pointer/word) and a
rooted Run at that exact origin, with a nonlocal/clock endpoint relation carried
from RecordEntry through PayloadEntry.Invocation and the existing result/endpoint
chain. Parameterize affected stage models/theorems by that origin; keep generic
Context/byte-list/math helpers independent. Then a final snapshot can be applied
to the actual root chosen by main, rather than merely some normal run for the
same input. Existing existential StatelessRun can remain as a compatibility
wrapper, with a rooted entry theorem retaining its relation to the real host-call
target. No such root selection equivalence is claimed yet.

## Witness snapshot reaches the original payload caller's actual post-state

PayloadCallerReturn retains its actual full payload body return, call arguments,
lookup, caller run and exact continuation-entry state. HashCountReturn retains
its prior payload caller and real payload-pointer store/lexical endpoint.
RequestsEntry retains its hash-count origin and all three actual metadata stores.
HashMetadataReturned identifies the original hash suffix's actual target using
the complete request call; PayloadSuffixReturned transports the witness snapshot
through the true nvh restoration; PayloadCallReturned resumes the complete actual
payload call and identifies its original caller target by deterministic evaluation.
The witness records/input/gas snapshot now belongs to that same Request.continuation
post-state. Earlier request-offset/record setup/header/full-stateless/main linkage
and transaction-record lifetime remain open. No global finite K.

Validation: current-payload-call-returned-v2.log PASS1452jobs/permitted printed
axioms;8GiBguard/twoslots/cachefalse. No full verification. Account19%weekly/
0resetcredits/ordinaryallowed. Overall40%, plausible30–50%.

## Witness facts joined to the actual enclosing request call

RequestCallerReturn.decoded now keeps its exact continuation-entry state rather
than only its memory. WitnessEntry retains the previous RequestCallerReturn.Result
and the exact rq-store state. WitnessRequestReturn rewinds header/code/node
scopes, loaded offsets, validator and witness declarations to that same original
request-caller post-state, with exact nonlocal/clock frame. WitnessSnapshot factors
this physical observation and transports it only with proved frames.
RequestCallReturned resumes the actual normally returned request callee and
identifies its original enclosing call's actual target by deterministic evaluation;
that complete Request.requestsCall returns Wordsi with the witness snapshot at
its actual post-state. Earlier hash/payload/request-prefix and full-stateless/main
run provenance still need composition; do not identify arbitrary existential
stage states with those actual main endpoints.

Validation: current-request-call-returned-v1.log PASS1449jobs/permitted printed
axioms;8GiBguard/twoslots/cachefalse. No global finite K or full verification.
Account18%weekly/0resetcredits/ordinaryallowed. Overall40%, plausible30–50%.

## All three actual witness lists through the final si return

WitnessHeadersReturn joins the genuine final hd call, si+72/80stores and literal
return si. It derives the actual returned stateless-record value, all three
physical record arrays and per-item bounds(1024nodes/65536code/1024headers),
headercount≤256, exact header pointer/count cells, protected original input and
payload gas, bounded post-heap beyond the header array, and a complete nonlocal
frame through return/caller restoration. Header-call sourcecost≤2*(sliceLength/4)+3.
The current decoder/main return joins, payload transaction-record retention and
whole-program target-step pricing remain open; this is no global finite K.

Validation: current-witness-headers-v2.log PASS1446jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. No full verification. Account18%weekly/0resetcredits.

Implementation note for the next join: the stage wrappers often return
existential intermediate states. Do not infer that a final physical record
belongs to an arbitrary particular main decoder post-state without an explicit
execution/endpoint relation. WitnessEntry currently retains prefix execution
but not its previous RequestCallerReturn.Result; add the missing provenance
when rewinding that store/caller. Earlier full-stateless return also needs an
explicit relation to the same main-derived source/post run, not just existential
normal-return facts for the same input. Preserve or parameterize the original
run endpoints while composing; no unproved identification of states/values.

## Second real witness list preserves node records

WitnessLive factors the five real witness-slice bindings; node-return summaries
now retain them, array separation, old-word frame and exact caller source cost.
WitnessSlices.arguments_between derives adjacent code/header list extents and
literal ABI from actual validated range/order and outer containment.
WitnessCodesReturn joins the real cd call and si+56/64stores: physical code
records,65536-byte item limits, prior physical node records/1024-byte bounds,
bounded frontier beyond the code array and after the node array, live slice
locals, protected input/gas and original parent endpoint. The real next suffix
is the header-list call. Header return/final stateless/main joins remain.

Validation: current-witness-codes-v1.log PASS1445jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. No global finite K/full verification. Account18%
weekly/0resetcredits/ordinaryallowed. Overall effort estimate remains40%(30–50%).

## First real witness list and both stateless-record output stores

WitnessSlices derives the contained node-list slice and literal ABI from the
actual validated offsets. WitnessNodesReturn applies the shared current byte-list
caller proof to the genuine st0 call and both si+40/48stores, retaining physical
node records,1024-byte item limits, actual pointer/count cells, input/gas Context,
original caller locals and parent endpoint, and the real next code-list call.
ByteListData/ByteListCall now retain the allocated array end as a lower bound
on the next bounded heap frontier; later arrays can therefore be shown disjoint
from earlier records. AllocationHeapControl factors this stronger end-bound
and common heap-maximum rule; superseded unused generic lower-bound rule removed.
Code/header lists and final stateless/main joins remain. No global finite K.

Validation: current-witness-nodes-v2.log PASS1443jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. No full verification. Account17%weekly/0resetcredits.

## Shared real byte-list caller return and field-store cleanup

CallerPairStores now checks Context preservation through the actual two tuple
field stores to si, using the existing genuine scalar-store rules. Validation:
current-witness-pair-context-v1.log PASS1440jobs/permitted printed axioms.


ByteListCall.normal rejoins an arbitrary actual current byte-list invocation
without minimum clock/future room: resumes its genuine continuation with the
saved caller locals and exact tuple, physical records/count/per-item bounds,
preserved prior memory and bounded aligned post-frontier. It transports the
shared caller Context and protected physical gas through the allocating call;
caller sourcecost≤2*(sliceLength/4)+3. CallerContextFields factors the immutable
field/input/gas/heap/live-local transport. Witness.Fields now imports only the
actual allocated-domain mapping helper rather than the AllocatedBytes umbrella
(which pulled an unrelated stale ZeroByteStore proof); OffsetValues imports
its actual syntax/offset predicate rather than the old normal-offset pipeline.

Validation: current-bytes-list-call-v4.log PASS1440jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. Three actual witness-list/store joins remain.
No global finite K or full verification; account17%weekly/0resetcredits.

## Actual loaded witness offsets and returned byte-list frontier

WitnessLoaded rejoins all three actual readonly offset declarations to the
real node-list call, with validated offsets, copied input, request/gas cells,
heap and exact parent endpoint frame. These loads spend no source ticks.
BytesList.RoomFromReturn exposes its real returning split-list allocation and
derives the persistent ceiling. Generic AllocationHeapControl factors bounded
aligned frontier transport for exact empty/nonempty allocation effects.
ByteListData.normal combines arbitrary-clock current byte-list return data with
that observed room: physical records, count/per-item limits, copied bytes and
old-memory frame, exact allocation/control, bounded post-heap and source cost
≤2*(sliceLength/4)+2. No future successful allocation/clock is supplied.

Validation: current-bytes-list-data-v1.log PASS1434jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. Actual three witness-list calls still need joining.
No global finite target K/full verification; account17%weekly/0resetcredits.

## Current witness offsets and arbitrary-clock byte-list returns

WitnessValidated joins the real three workspace writes/offset validator to the
main-derived witness entry: first offset12, all three validated ranges/order,
actual loaded-body continuation, prefixcost≤8source ticks, exact control/endpoint
frames, original input, bounded allocator frontier and preserved physical request
and payload-gas cells. Shared CallerContextControl factors the nine-live-local
control-frame transport. OffsetLoop imports PanControl explicitly; LoadedOffsets
now imports only actual syntax, workspace read and declaration dependencies.

BytesList.Program/OriginalCode now use current Software decode_bytes_list189.
BodyNormal and CallerNormal pass the real bounded incoming heap and installed
trap entry to the current variable-list allocator theorem. NormalAnyClock removes
minimum-clock funding via checked clock padding: exact returned tuple/records,
count/per-item limits, input/old-word frame, allocation/control and body source
cost≤2*(sliceLength/4)+2for an actual normal return at any clock. The real three
witness-list entry/return joins and their derived post-allocation frontier remain.

Validation: current-bytes-list-normal-v2.log PASS1433jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. No global finite K or full verification.

## Real witness entry and dependency cleanup

OuterLocals now retains actual p/len/o_wit plus validated input containment,
derived from the real six-action record setup and propagated through payload,
fixed-count/request returns and shared Context memory/local frames. The original
request decoder's scoped caller now retains these facts too. WitnessEntry checks
the actual request-pointer store and full witness declaration/short-length-guard
suffix: derives the12-byte minimum and actual contained wp/wlen, preserving
original input, heap, protected gas and exact endpoint memory/clock observations.
The three variable witness-list decodes and final stateless/main join remain.

Witness.Program and OffsetProgram now use current Software syntax and minimal
independent BytesList.Values, rather than importing historical byte-list array
execution theorems just for syntax. Existing values namespace/API retained;
Environment imports that definition explicitly. PrefixNormal now imports its
actual guard/declaration dependencies. Solver closures: Program168→109,
OffsetProgram208→110, PrefixTrace213→113; manifest records exact compared sets.
Historical BytesList.Environment/caller runtime proofs are not revalidated here.

Validation: current-witness-entry-v1.log PASS1414jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. No full verification/global K. Account17%weekly/
0resetcredits/ordinaryallowed. Overall40%, plausible30–50%.

## Actual request return resumes its stateless-input caller

RequestCallerReturn rejoins the complete request decoder to the original
scoped rq call and real afterRequests suffix. It retains the ten-field decoded
record through an exact memory frame, current request/record ownership and
allocation frontier, original input, and physical payload gas≤200000000.
No successful future witness decode is assumed. Next: retain outer witness
locals through earlier checked summaries, then derive the three witness slices.
Validation: current-request-caller-v3.log PASS1406jobs/permitted printed axioms;
8GiBguard/twoslots/cachefalse. No global K/full verification.

## All-outcome scratch clear and constructor source bounds

ZeroUnmappedCost now checks the full first-loop result (including timeout's
empty locals), then the complete current memzero body: only error/timeout,
source cost≤1body/2caller ticks at an aligned below-domain clear of≥32bytes.
ScratchClearCost derives each actual returned scratch allocation before pricing
that clear, and proves cost≤4for the complete allocation/clear with arbitrary
unreachable suffix. Real msg_new_scratch body≤4; frame_new's two genuine cursor
marks add2, giving body≤6on every outcome. The reusable mark pricing rule also
replaces duplicated clock case analysis in ScratchNodeFill. No future allocation
room/success/mapped scratch or later EVM operation is assumed.

Validation: current-scratch-constructor-cost-v3.log PASS822jobs/permitted printed
axioms; two slots/cachefalse/8GiBguard. Index7970modules/15834facts; replacement
closure0/frozenmainunchanged. Account17%weekly/0resetcredits/ordinaryallowed.
No global K/full verification; overall40%, plausible30–50%.

## Actual main hash cut retains the initialized arena values

CurrentHash checks the closed31-helper htr_new_payload_request graph at the
current Software declarations, with8existing startup helper proofs reused.
Both arena globals are preserved on every outcome. HashPrefix reconstructs
main's actual root allocation and request hash call, then splits every genuine
source termination into earlier stops or the real post-hash verification suffix,
retaining lexical execution, initialized arena values, outcome, clock and FFI
observations. No successful hash/decoder/clock is assumed.

Validation: current-hash-main-cut-v1.log PASS377jobs/permitted printed axioms,
4.45s/MaxRSS1536144KiB;8GiBwhole-hostguard/twoslots/cachefalse. Index7966modules/
15826facts; inventory8004/replacementclosure0/frozenmainunchanged; incremental
policy PASS64773entries/2482043726bytes. No full verification/global K.

## Actual node encoder scratch boundary

ScratchStore derives a below-domain error from an actual normal scratch
allocation followed by a literal in-record scalar store; no future allocation
room or successful clock premise. The complete scoped allocation/store costs
at most two source call/loop ticks on every outcome. Arenas.Cost now references
actual Guest.Software declarations. ScratchNodeFill checks actual declaration258
and scratch_mark9, deriving no normal return and all-outcome body cost≤3 before
its later traversal loop. Actual caller arena transport remains open.

Validation: current-scratch-node-fill-v2.log PASS1434jobs/permitted printed axioms,
4.14s/MaxRSS1676076KiB;8GiBwhole-hostguard/twoslots/cachefalse. No global K or full
verification. Overall40%, plausible30–50%; account16%weekly/0resetcredits.

## Complete current request return:348source ticks and exact physical fields

The current five-count suffix checks on every non-timeout outcome (real list
error or complete ten-field output), cost≤335source call/loop ticks and exact
outside-memory/control frame. DecoderRuntimeCode now imports actual minimal
parser/division syntax and current declaration entries (185/186for variable/
fixed lists), adding fail179/offset184entries. CountsTrace uses that fail entry
instead of MainDecoderCall. StructureStore uses real HeapFrame/ScalarProgram/
LocalWord/AllocatedArena imports. TerminatingPaddedScopeArgs uses explicit
clock-zero cases, avoiding an implicitly imported by_contra tactic. Existing
APIs retained. Cleanup closure counts: DecoderRuntimeCode357→83, CountsTrace
743→109, StructureStore124→34; manifest records compared sets.

RequestsValidated/Allocation/CountsEntry now retain exact control and prefix
clock price alongside the actual original endpoint. RequestsReturned joins the
five actual count calls and ten output stores to the complete decode_requests
body return: actual record pointer, all ten physical cells, quotient/remainder
facts, copied bytes, aligned bounded post-heap beyond the80-byte record, protected
payload gas word, exact allocation/control effect and body source-clock cost≤348.
This is a complete normal request return, not a global main target-step bound.

Validation: current-requests-returned-v2.log PASS1406jobs/permitted printed axioms,
14.30s/MaxRSS1924444KiB;8GiBwhole-hostguard/twoslots/cachefalse. Index7938modules/
15784facts; inventory7975/replacementclosure0/frozenmainunchanged; incremental
policy PASS64743entries/2481880685bytes. No full verification/global finite K.
Account16%weekly/0resetcredits/ordinaryallowed. Overall40%, plausible30–50%.

Next inspect the earliest actual scratch constructors/callers and covered-outcome
consequences before expanding the remaining decoder/map/crypto work. Actual main
DecoderPrefix already carries ArenaState through the complete caught decoder on
all outcomes, independently of physical decoded layout; this may allow an earlier
execution cut. Do not infer whole-path exclusion from constructor NoReturn alone.
Pending dataflow: request caller, three witness lists/stateless/main, complete
payload tx records/count. Source/all-outcome and weighted target bounds remain.

## Actual80-byte request allocation and real count-call entry

RequestsAllocation inverts the actual scoped allocation, deriving the incoming
cursor, real80-byte room≤2952790016, exact caller update and next aligned frontier
beyond the full request record. It preserves original input, workspace cells,
installed metadata, p/len and the earlier bounded payload gas word. No future
allocation room or clock is supplied. Original request endpoint/frame remains.

LayoutProgram extracts shared actual allocation/load/count selectors from the
old allocator-bearing SetupProgram; both syntax modules check against Software.
CountProgram now imports LayoutProgram directly and selects current Software.
OffsetLocals executes only the five readonly declarations with PanDeclarations
and proves their actual CountLocals model. RequestsCountsEntry joins this to the
real already-allocated state at original clock, preserving gas/input/heap and
full request endpoint. WorkspaceWord moves the generic Request.word_read lookup
out of RequestLoad's allocation-prefix import; old consumers retain that API.
RequestLoad reexports it. The old allocation execution Setup is not revalidated.

Validation: current-requests-counts-entry-v2.log PASS1392jobs/permitted printed
axioms,4.77s/MaxRSS1912972KiB;8GiBwhole-hostguard/twoslots/cachefalse. Index7937/
15780facts; inventory7974/replacementclosure0/frozenmainunchanged; incremental
policy PASS64742entries/2481870203bytes. Failed diagnostics unindexed; no full
verification or global finite K. Account15%weekly/0resetcredits/ordinaryallowed.
Overall40%, plausible30–50%.

Next current five fixed-list count calls/output and complete request return,
protecting the payload gas cell and real count arithmetic. DecoderRuntimeCode /
CountsTrace still import old whole payload/main proof umbrellas; replace with
minimal current code-entry proofs before selected checks. Then request caller,
three witness lists/stateless/main. Still need whole-payload tx records/count;
scratch covered-outcome analysis stays prioritized before map/crypto migration.

## Current five-offset loop/validator and protected payload gas cell

Requests.OffsetStep/OffsetLoop/LoopTrace now check the actual five scratch-word
writes, byte correspondence, full outside-memory/control frame and loop price.
OffsetStep imports LocalWord explicitly; OffsetLoop imports PanControl and closes
its reflexive clock bound explicitly. LoopTrace imports its pure declaration rule.
WhileActive replaces the unused scalar input/heap scope import with Guest.Model,
StateSteps and the evaluator equations, preserving the real while-resumption API.
OffsetsTrace's literal selector now uses Software.

RequestsValidated joins this to the real main-derived request entry at its
original clock: actual first20offset and all five range/order guards, physical
workspace cells, original input, installed metadata, bounded post-payload heap,
live p/len and actual allocator continuation. Workspace writes preserve the
separate payload gas cell by the derived record/input/workspace geometry. It
also retains the original request callee endpoint/frame for full return joins.
No new readability, future time, allocation room or successful-call assumptions.

Validation: current-requests-validated-v2.log PASS1384jobs/permitted printed
axioms,4.83s/MaxRSS1925656KiB;8GiBwhole-hostguard/twoslots/cachefalse. Index7932/
15772facts; inventory7969/replacementclosure0/frozenmainunchanged; incremental
policy PASS64737entries/2481850402bytes. Failed logs unindexed; no full verification
or global finite K. Account15%weekly/0resets/ordinaryallowed; disk60%.
Overall40%, plausible30–50%.

Next derive the actual80-byte request allocation room/frontier from its normal
return, retain pure five offset loads and five fixed counts/output, then request
resumption/witness lists/stateless/main. Physical tx records/count at complete
payload return are still needed for the later tx loop; current Context retains
the actual bounded gas but not the full payload image. Scratch coverage remains
prioritized before map/crypto migration and weighted target-bound composition.

## Actual request decoder entry and dependency cleanup

RequestRequestsProgram selects the genuine three stores after nvh and the
actual decode_requests call. RequestsEntry derives those stores using the
shared stateless-field rule, retains input and the bounded physical gas word,
derives start=18+le32(input,58)and size=le32(input,6)-16-le32(input,58)within
the copied extent, and inverts the real length guard to size≥20at original
clock. It retains actual callee args/lookup and caller return for later resumption.
CallerLocals now retains the actual outer request upper bound too.

Requests.Program now uses Software and its actual declaration index188, with
OriginalEntry, HeaderProgram and AllocatedArena imports replacing the old whole
DecoderRuntimeCode/AllocatedBytes umbrellas. Its transitive Solver closure falls
359to64modules. NonTimeoutSequenceCall imports only PanState plus the evaluator's
actual equation module; unused padded-clock/exhaustion proof dependencies are
removed. Direct clock-zero cases replace an implicitly imported by_contra tactic.
Sequence/scoped timeout helpers retain their APIs and fall10to2/11to3Solver
modules. The cleanup manifest records the compared checkpoint/import sets.

Validation: current-requests-entry-v5.log PASS1378jobs/permitted printed axioms,
5.06s/MaxRSS1913712KiB;8GiBwhole-hostguard/twoslots/cachefalse. Index7931modules/
15770facts; inventory7968/replacementclosure0/frozenmainunchanged; incremental
policy PASS64736entries/2481843040bytes. Failed diagnostic logs unindexed; no
full verification or global finite K. Account15%weekly/0resets/ordinaryallowed.
Overall estimate40%, plausible30–50%.

Next real five-offset loop/validator, deriving its80-byte allocation room from
observed return rather than ordinary backing. Then fixed counts/output, request
resumption, three witness lists and complete stateless/main return. Still need
physical transaction records/count at complete payload return for later tx-loop
bounds; current Context retains actual bounded gas but not the full payload image.
Prioritize earliest scratch covered-outcome consequences before map/crypto work.

## Real hash-count caller and shared request-context frames

PayloadEntry.CallerLocals retains the actual np/nlen/o_vh/o_rqbindings and three
offset guards. PayloadCallerReturn now shares a named Context, keeping those
bindings and the real ssz_offs global through the complete payload body via the
checked current global-effect theorem. Pure-call frames and memory/clock frames
are shared, including an actual scalar stateless-record store rule. Its copied
input/gas separation derives from original allocation geometry.

RequestHashesProgram selects the actual store(si+0,pl), then the real nvh fixed-
list call. HashCountReturn executes that store, preserves the separate physical
gas word and resumes after the actual32-byte hash-count call. It derives count=
(le32(input,58)-le32(input,22))/32and remainder0from actual validated offsets and
normal return; cost≤66source clocks with no minimum clock or future room premise.
No guest change. Request/witness/stateless/main joins and global target K remain.

Validation: current-hash-count-return-v3.log PASS1371jobs/permitted printed axioms,
8.06s/MaxRSS1931584KiB;8GiBwhole-hostguard/twoslots/cachefalse. Index7929modules/
15767facts; inventory7966/replacementclosure0/frozenmainunchanged; incremental
policy PASS64734entries/2481831635bytes. No full verification or global finite K.
Account14%weekly/0resetcredits/ordinaryallowed. Overall40%, range30–50%.

Next actual hash-pointer/count/header stores and decode_requests entry/body, then
three witness-list calls and complete stateless/main return. Retain actual record
cells and gas lifetime; prioritize earliest scratch covered-outcome analysis.

## Real payload caller resumption and stateless/payload record ownership

RequestCut now retains the real post-allocation frontier beyond the96-byte
stateless record; RecordEntry carries it through its actual length guard.
PayloadEntry retains this frontier and real caller si binding/record geometry.
PayloadCut also exposes the incoming heap cell; Endpoint retains that exact
payload allocation pointer through all nested returns. All are derived from
actual execution, without new future-success/room premises.

PayloadCallerReturn resumes the real enclosing Request.afterPayload with its
actual returned pl binding, copied bytes, installed code/shapes/domain/endian,
bounded aligned heap beyond the136-byte payload, physical gas cell≤200000000
and real si binding. It proves si+96≤pl and both records' alignment/room. This
is the real request continuation, before its remaining count/request/witness
calls; it does not yet claim full stateless/main return or a global target bound.

Validation: current-payload-caller-return-v1.log PASS1369jobs/permitted printed
axioms,4.83s/MaxRSS1909216KiB;8GiBwhole-hostguard/twoslots/cachefalse. Index7927/
15759facts; inventory7964/replacementclosure0/frozenmainunchanged; incremental
policy PASS64732entries/2481813901bytes. No full verification or global finite K.
Account14%weekly/0resetcredits/ordinaryallowed. Overall40%, range30–50%.

Next retain actual caller offset/length locals and workspace through the payload,
then the fixed hash-count call, decode_requests and three witness-list calls,
protecting the actual payload gas cell through later writes. Continue toward
main run_attempt; earliest scratch covered-outcome analysis remains prioritized.

## Complete actual payload return retains its physical bounded gas word

PayloadEntry.Result indexes the original actual payload entry/poststate and
retains its enclosing request invocation. Endpoint records the same nonlocal
poststate and clock through lexical scopes. Workspace, validated offsets,
extra-data, transaction callee/caller and withdrawal return now carry that
endpoint; real call resumption proves its restoration frame.

PayloadGasReturned.complete joins all eleven suffix stores to the complete
current decode_payload body return at the original clock. It proves the actual
returned record's gas cell is le64(input,474), with copied input and the bounded
aligned heap beyond the136-byte record. separated_complete joins original gas
and canonical offsets to gasWord.toNat≤200000000at that complete return. This
closes the prior suffix-only limitation; request/stateless/main return joins,
record lifetime, global all-outcome source and weighted target bounds remain.

Validation: current-payload-complete-gas-v1.log PASS1368jobs/permitted printed
axioms,45.42s/MaxRSS1942456KiB;8GiBwhole-hostguard/twoslots/cachefalse. Index7926/
15756facts; inventory7963/replacementclosure0/frozenmainunchanged; incremental
policy PASS64731entries/2481804875bytes. No full verification or global finite K.
Account14%weekly/0resetcredits/ordinaryallowed. Overall40%, range30–50%.

Next resume the real enclosing request call with its bounded-gas payload, derive
record separation/lifetimes and continue to actual main run_attempt. Prioritize
scratch covered-outcome analysis before expanding map/crypto work.

## Real transaction caller, withdrawal count and physical gas store

TransactionReturn resumes the actual list caller at its original clock, with the
returned tuple, live payload Context, copied image, initialized records, valid
four offsets, protected payload words and actual price≤slice/4+2. TransactionEntry
and VarListData retain original offset validation. PayloadStoreFrame shares known
field-store/context proofs; Context.locals_clock shares seven live-binding frames.
Records.store_before preserves initialized arrays across earlier field stores.

WithdrawalReturn follows both actual tuple-field stores and the real fixed-list
count call, retaining physical transaction fields/records, copied bytes, division
facts and actual cost≤66. FixedList.NormalAnyClock removes clock funding through
checked extension. UDivMod/FixedList literal checks now use Software; division
syntax drops the unrelated payload allocator-prefix imports. Transaction stores
import their actual word-store/environment dependencies; old WithdrawalsNormal
now imports its caller theorem explicitly. PayloadWordStore imports PanControl
explicitly. RemainingProgram uses Software and RemainingExecute imports its raw
byte arithmetic directly.

PayloadGasReturned checks all eleven remaining real stores and actual suffix
return: gas at record+88 is the copied le64(input,474), bounded≤200000000from the
main-derived canonical offsets and original gas premise. Input and bounded heap
remain. This is the actual returned suffix; connecting its state to the complete
payload/request/stateless/main return is still required. No global finite K.

Validation: current-payload-gas-return-v2.log PASS1368jobs/permitted printed axioms,
4.44s/MaxRSS1888216KiB;8GiBwhole-hostguard/twoslots/cachefalse. Index7926modules/
15753facts; inventory7963/replacementclosure0/frozenmainunchanged; incremental
policy PASS64731entries/2481797419bytes. Old unselected whole-body/caller/image/
trace proofs remain historical. No full verification. Account13%weekly/0resets.
Overall effort estimate40%, plausible30–50%; source clock costs are not target K.

Next connect complete actual payload return/physical layout and enclosing decoder
calls, then earliest scratch-call covered-outcome analysis before map/crypto work.

## Actual returned transaction records and allocation-room composition

Allocation.allocation_execute now requires the real allocator ceiling separately
from ordinary backing geometry. BodyNormal derives that room from the observed
returned execution, incoming bounded heap and installed trap body. NormalSummary,
Records, NormalAnyClock and CallerNormal now carry those real prerequisites;
NormalAnyClock removes a supplied clock budget using checked clock extension.

CurrentStartup.VarListData joins those proofs to the genuine main-derived list
callee: actual returned pair/physical records, original input, earlier-memory
frame, exact allocation control, bounded aligned post-heap beyond the136-byte
payload record and source-clock price≤slice/4+1. Its Result structure retains
actual caller invocation/return and slice positions for the next continuation
proof. TransactionEntry now retains that invocation instead of discarding it.
This changes proof interfaces only; no guest/ROM/semantics/claim changes.

Validation: current-transaction-data-v3.log PASS1314jobs/permitted printed axioms;
8GiBwhole-hostguard/twoslots/artifactcachefalse. Index7922modules/15740facts;
inventory7959/replacementclosure0/fixedfilesunchanged; incremental policy
PASS64727entries/2481765738bytes. Old unselected body/caller traces remain
historical. No full verification or global finite K; estimate40%, range30–50%.
Account13%weekly/0resetcredits/ordinaryallowed. Push each commit.

Next resume Payload.afterTransactions at the actual clock with its returned tuple,
preserved context and record/input memory; then withdrawal count and gas stores.

## Current allocated-list loop/tail and reusable allocation-room inversion

VarList.StepProgram's literal checks now use Software. The real dynamic offset
reads, record stores, valid/error bodies, arbitrary remaining loop rounds, final
length cell and pair return all pass through AllocatedTail. The theorem retains
copied input, the exact prior-memory/array frame, control and source-clock price
≤count+1for that already-allocated tail, with real SszErr23alternatives. It does
not claim that the allocator has enough room from ordinary backing alone.
A missing reflexive clock inequality in AnyLoop is now closed explicitly.

LocalWord extracts the unchanged generic Request.local_word lookup from the
unrelated request-offset store module; old consumers retain that namespace/API.
OffsetRead/StepStores import its two-module Solver closure explicitly. AllocatedTail
uses generic PanDeclarations for its i/prev scopes and drops the unused allocator
prefix namespace; ValidBody/FaultBody drop the same unused namespace. The room
inversion moves to VarList.RoomFromReturn with explicit real allocator/trap/fail
entries, exception shape and current bounded heap. CurrentStartup.VarListRoom is
now the genuine-entry wrapper. The generic105-module closure imports no Current-
Startup module, so body/caller proofs can reuse it without the whole-main graph.
[Cleanup manifest](current-varlist-loop-cleanup-20261027.json) records these sources.

Validation: current-varlist-allocated-tail-v4.log PASS1305jobs/permitted printed
axioms,14.05s/MaxRSS1638508KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Both
AllocatedTail and CurrentStartup.VarListRoom are selected, checking the moved
lookup/room proofs and the existing main join together. Failed diagnostics
unindexed. Index7921historical/currentmodules/15738facts,416current-reference
modules; inventory7958/replacementclosure0/frozenmainunchanged; incremental policy
PASS64726entries/2481756902bytes. No full verification or finite global K.
Account12%weekly/0resetcredits/ordinaryallowed. Five old untracked RLP files retained.
Push each commit.

Next make the actual allocator execution API require its real ≤2952790016request
room separately from Plan.arrayRoom's ≤33806089496ordinary mapping bound. Derive
that semantic room from RoomFromReturn in nonempty normal body/caller summaries,
using actual incoming heap bound and trap code (both available at TransactionEntry).
Retain empty-list handling and remove padded-clock assumptions through the proved
clock-shift theorem. Old whole-body/caller/trace helpers are not claimed checked.
Then real returned records/array frame to payload continuation, withdrawal count
and gas stores; scratch covered-outcome classification/global target work remain.
Overall estimate40%, plausible30–50%.

## Genuine variable-list guards and current allocator room

VarList.Entry imports its real HeaderGuards/PanDeclarations dependencies. Entry
and FirstGuards use generic BuildEntry declaration execution for their first/count
locals instead of importing the allocator-bearing ProgramPrefix umbrella just
for pure local scopes. The actual empty/length/first/count entry inversion and
encoded-count facts now pass against Software with these explicit dependencies.

CurrentStartup.VarListRoom.returned_room adds one checked clock unit to an
observed returned body to fund guard inversion. It either exposes the genuine
empty pair, or derives length≥4, positive count, first=4*count≤slice length and
count≤actual limit, followed by the real scoped allocation. It reads the actual
count*16 request, uses the existing scalar/aligned/bounded incoming heap from
main and the real installed allocator/trap code, then inverts that observed
allocation return. The conclusion is **array+16*count≤2952790016**, with the
array cursor beyond the136-byte payload record. It assumes neither whole-array
room nor future allocation/loop success. Its transaction projection applies this
directly at the actual main-derived callee, preserving the real empty alternative.
The allocated loop/returned tuple/record frame are not yet composed.

Validation: current-varlist-room-v3.log PASS1279jobs/permitted printed axioms,
4.67s/MaxRSS1873904KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Failed import/
scope diagnostics unindexed. Index7919historical/currentmodules/15737facts,
390current-reference modules; inventory7956/replacementclosure0/frozenmainunchanged;
incremental policyPASS64724entries/2481753769bytes. No complete verifier or finite
uniform target K. Account11%weekly/0resetcredits/ordinaryallowed. Five old untracked
RLP files retained. Push each commit.

Next check allocated-tail/loop/records against current syntax and factor the
room inversion for reuse by normal summaries. Preserve the distinction between
ordinary backing≤33806089496and actual allocator room≤2952790016. Incoming actual
code/trap/heap prerequisites can be derived at the genuine transaction entry;
static loop/record helpers must not assume future room/success. Then withdrawal
count and gas stores. Also check earliest actual scratch calls and their covered
terminal FFI/error consequences before expanding current map/crypto obligations.
Overall40%, plausible30–50%; global weighted target composition remains open.

## Real transaction-list callee and heap frontier beyond payload record

AllocationFrontier.after now retains the post-allocation frontier beyond the
entire returned record, using observed room and actual alignment rounding.
PayloadCut carries that stronger pl+136frontier through the two stores/four
reads and records it in Context.recordHeap. remainder_heap shares the pure
suffix proof rather than duplicating it inside the allocation rule.

Context.op_store derives an actual scalar-operation store's memory update and
copied-byte separation from the current record geometry, then retains all other
Context facts. TransactionEntry applies it to real extra-data pointer/length
stores at pl+16/pl+24, using their observed normal prefix executions. Actual
four-offset ordering and slice containment derive the real variable-list p/len
arguments. Real enclosing return supplies scoped-call funding; the installed
Software function and checked parameter environment identify the true callee.
At that entry, original copied bytes and heap≥pl+136remain available, p points
to the contained transaction slice, len is its real byte length and lim is the
actual9223372036854775807literal. Its actual returned body is exposed. No whole-
array room, successful future list parsing/return or clock allowance is assumed.

Validation: current-transaction-entry-v2.log PASS1271jobs/permitted printed axioms,
4.65s/MaxRSS1881128KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Components
payload-record-frontier-v1 PASS1266, payload-store-context-v1 PASS1267. Failed
extent diagnostic unindexed. Index7918historical/currentmodules/15735facts,
382current-reference modules; inventory7955/replacementclosure0/frozenmainunchanged;
incremental policyPASS64723entries/2481747581bytes. No complete verification or
finite global K. Account11%weekly/0resetcredits/ordinaryallowed. Five old untracked
RLP files retained. Push each commit.

Next invert the real variable-list length/first/count guards and actual allocation
to derive room for16*countwithin2952790016. The old ordinary-memory premise
array+4*slice≤33806089496is coarse (and can follow from current heap/input bounds)
but does not by itself fund the smaller actual allocator ceiling. Reuse checked
allocated-loop/record proofs after resolving that distinction; include the real
empty-list branch. Then fixed withdrawal count, remaining gas stores/record joins,
scratch covered outcomes and global current-program quantitative target work.
Overall40%, plausible30–50%.

## Actual extra-data size guard and variable-list entry dependency cleanup

PayloadExtraGuard's literal shape now uses Software; its import is reduced to
PayloadOffsetsNormal instead of the unrelated old whole-prefix bridge.
CurrentStartup.PayloadExtra applies GuardActual to the real returning continuation,
deriving extra-data length≤32at the original source clock. It retains Context,
all four actual offset validity facts and the genuine next payload run. No extra
fuel or future helper-return premise is introduced.

DropLeading extracts the unchanged generic lexical-tail selector from the payload
prefix module. VarList.Program uses that small helper, HeapFlatScalar and actual
Software variable-list syntax. VarList.Environment imports the actual Program and
CodeEnvironment directly instead of its unrelated NormalSummary/CallNormal
umbrella. The historical CallerNormal now imports its used NormalSummary explicitly;
its runtime/room premises are not revalidated at this checkpoint. PayloadTransactions
Program imports the parameter environment, uses actual Software and raw-list
Framing.le32_lt. Its true transaction/withdrawal call shapes and argument arithmetic
pass; the genuine transaction call/array ownership proof remains next.

[Cleanup manifest](current-varlist-entry-cleanup-20261027.json) records old imports,
revision and current hashes: VarList.Program74to20, Environment109to21,
PayloadTransactionsProgram127to88Solver modules. PayloadExtraGuard85to84. These
are proof dependency changes; fixed guest/semantics/ROM/proofs/Solution/claim are
unchanged. Historical variable-list body/caller cost summaries are not claimed
current merely because their entry module builds.

Validation: current-payload-transaction-program-v1.log PASS1269jobs/permitted
printed axioms,39.31s/MaxRSS1894148KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse.
Component payload-extra-v1 PASS1265. Index7916historical/currentmodules/15729facts,
380current-reference modules; inventory7953/replacementclosure0/frozenmainunchanged;
incremental policyPASS64721entries/2481736437bytes. No complete verification or
finite global K. Account11%weekly/0resetcredits/ordinaryallowed. Five old untracked
RLP files retained. Push every commit.

Next retain copied bytes through the two extra-data header stores and extract the
real transaction-list callee. Strengthen the heap frontier beyond the actual136-
byte payload record to protect it against later array writes. Derive genuine list
allocation room from its actual returned call; the old sufficient whole-array room
premise is not a free incoming invariant. Then fixed-list count and remaining gas
stores, genuine main records and scratch covered-outcome classification/global
quantitative target composition. Overall40%, plausible30–50%.

## Real payload offset locals, four workspace stores and fixed540guard

PayloadOffsetsProgram now imports only the literal PayloadPrefixProgram instead
of the old full PayloadPrefixSetup bridge, and retargets its shape to Software.
Header/offset stores explicitly import their used generic RequestOffsetsStores
helpers; PayloadOffsetsNormal explicitly imports the generic state_from_frame
lemma. The actual read/declaration/stores/validator helpers pass with these
dependencies, without silently checking the old whole allocation-setup bridge.

PayloadOffsetsLocals identifies all four real byte-offset declarations with raw
input fields498/566/570/590. Its actual trace retains the byte image and p binding;
read-only lexical updates leave that image intact, so each observed value follows
from the same input bytes. PayloadWorkspace now retains the four locals in a
shared Context with metadata, copied image, heap/record geometry and p/len/pl.
Context.memory_clock transfers its nonmemory facts while requiring the actual
resulting input image; no memory-frame assertion is invented by that transfer.

PayloadValidated joins the real four workspace stores and count4/fixed540validator
to the main-derived state. Each rejected10/11/12outcome contradicts actual return;
passing derives offsetWords0=540, raw le32(input,498)=540and every actual range/
ordering fact. The real following payload continuation retains original copied
bytes, all Context metadata/geometry/locals and the actual returned body run.
No future funding, validated values, mapping or successful helper is a premise.
The extra-data size guard, transaction array, remaining payload records and gas
store still need actual-entry byte/ownership proofs.

Validation: current-payload-validated-v2.log PASS1263jobs/permitted printed axioms,
9.83s/MaxRSS1877572KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Components
payload-offsets-v2 PASS709, payload-offset-locals-v1 PASS1256. Failed diagnostics
unindexed. Index7915historical/currentmodules/15727facts,375current-reference
modules; replacementclosure0/frozenmainunchanged; incremental policyPASS64719
entries/2481733835bytes. No full verifier run or finite target K. Account11%weekly/
0resetcredits/ordinaryallowed; five old untracked RLP files retained. Push each
commit. Next extra-data guard and transaction-list allocation/decoding/image
lifetime, fixed withdrawal count and remaining scalar/gas stores. Scratch
covered-outcome/global quantitative target composition remain open. Overall40%,
plausible30–50%.

## Real payload record and input image through its header/offset loads

PayloadPrefixProgram now imports actual PayloadProgram and generic ProgramPrefix
syntax instead of the unrelated RequestGasFromHeader bridge; its shape proof uses
Software. [Cleanup manifest](current-payload-prefix-cleanup-20261027.json) records
the exact prior import/revision, current hash and Solver closure85to72. The older
whole-payload/gas bridge is not revalidated by this cleanup.

PayloadCut reconstructs the real seven actions after the passed length guard:
alloc136, pointer/length stores, and four flattened byte-offset declarations.
Actual payload return exposes their live lexical execution, original clock/frame
and retained lower heap frontier. AllocationFrontier derives the observed pl
pointer, whole136-byte room and alignment; later actions preserve that binding.
InputImageFrame.word_store_separate shares the exact observed ordinary word-store
frame and physical byte separation. PayloadHeaderImage applies it to both header
stores, using the actual p/len bindings, then retains bytes through all four real
reads. No future mapping, room, field read or store success is assumed.

PayloadWorkspace joins these to the main-derived PayloadEntry. The actual offset
body now has original copied bytes, genuine code/domain/endian/exception metadata,
ssz_offs2701132528, correct p/len/pl and allocator frontier, contained540-byte-or-
larger slice and separate136-byte record. It exposes the real continuing body.
The next four workspace stores, offset validator, transaction/list allocations
and later scalar field/gas store still need their actual-entry byte frames.

Validation: current-payload-workspace-v1.log PASS1254jobs/permitted printed axioms,
4.87s/MaxRSS1876448KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Components
payload-prefix-program-v1 PASS672, payload-cut-v2 PASS1252, payload-header-image-v2
PASS1253. Failed diagnostics unindexed. Index7913historical/currentmodules/15722
facts,366current-reference modules; inventory7949/replacementclosure0/frozenmain
unchanged; incremental policyPASS64717entries/2481722057bytes. No full verifier
run or finite global K. Account11%weekly/0resetcredits/ordinaryallowed. Five old
untracked RLP files retained. Push each commit. Next the real four-offset payload
workspace writes/validator, then remaining array/header/scalar stores to gas.
Scratch covered-outcome classification/global target composition remain open.
Overall estimate40%, plausible30–50%.

## Genuine payload callee, minimum slice and copied image

PayloadGas/Program now use actual Software payload syntax. PayloadProgram imports
its PayloadGas and HeaderGuards dependencies explicitly; the unrelated request
bridge import is dropped. Lean checks the actual gas-store expression/position
against the fixed current AST, and the reusable ordinary copied-byte gas-read
lemma. This does not establish that the later gas store is reached with its
byte image intact.

CurrentStartup.PayloadEntry joins the real request-offset trace to actual payload
arguments, derives real scoped-call funding from enclosing return, and extracts
the genuine decode_payload callee via its installed code and checked p/len
parameter environment. GuardActual excludes the real short-payload rejection
without extra minimum-clock premises. It derives p=input+62, raw slice length
le32(input,22)−44≥540, contained slice≤encodedlength−62and encodedlength≥602.
At the actual afterGuard entry it retains original copied bytes, byte order,
ordinary domain, installed code/exception shapes, actual ssz_offs pointer and the
post-copy heap frontier beyond input+encodedlength+8. The callee's real returned
run is exposed; no future allocation room, payload validity or read is assumed.

Validation: current-payload-entry-v2.log PASS1250jobs/permitted printed axioms,
5.45s/MaxRSS1887100KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Component
current-payload-program-v1 PASS665. Failed v1 projection diagnostic unindexed.
Index7910historical/currentmodules/15711facts,362current-reference modules;
replacementclosure0/frozenmainunchanged; incremental policyPASS64714entries/
2481704812bytes. No full verification or finite global target K. Five old untracked
RLP files retained. Account11%weekly/0resetcredits/ordinaryallowed. Push eachcommit.

Next derive the real136-byte payload allocation, copied-image frame through its
header/workspace/array stores, and actual gas read/store. Then connect returned
payload/request/stateless records to later genuine main helpers. Scratch covered-
outcome classification, current crypto/maps and global weighted target bounds
remain open. Overall estimate40%, plausible30–50%.

## Actual request length, second canonical offset and raw gas field

RequestPositions inverts the real lexical declarations and derives np=input+18
and nlen=raw witness offset−16. The actual allocation and chain-ID store preserve
the necessary caller locals; original outer workspace loads derive their words
from the preceding checked stores. RecordEntry now applies GuardActual to the
real request-length guard, deriving nlen≥44and encodedlength≥62and exposing the
actual request body at its original clock with copied bytes still intact.

RequestOffsetsProgram drops the unrelated RequestFromHeader bridge and imports
RequestPrefixProgram directly. RequestOffsetValues retargets its literal payload
call shape to actual Software and replaces stale HostGas backing equations with
the proved raw-list Framing.le32_lt. The real three offset declarations/stores,
their input-byte frames and all-outcome validator trace now pass against current
source. CanonicalRequest joins them to RecordEntry: raw offset at18=44, next
payload end at22≥44and≤requests offset at58≤actual nlen. Rejected validator
outcomes contradict an actual returned decoder rather than being assumed absent.

CanonicalRequest.separated_offsets derives both canonical16/44offset facts from
the whole-main stateless run. gas_field then derives le64(input,474)≤200000000
from the original declared-gas premise. This is a bound on the mathematical raw
eight-byte field, not a claim that its actual later payload read/store or EVM gas
accounting is joined yet. Need the payload-entry allocation/image/length proof.

Validation: current-canonical-request-v1.log PASS1245jobs/permitted printed axioms,
4.69s/MaxRSS1874032KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Components
current-request-entry-v1 PASS1238and request-offsets-v1 PASS696. Failed diagnostics
unindexed; no limits increased. Index7909historical/currentmodules/15708facts,
357current-reference modules; replacementclosure0/frozenmainunchanged. Incremental
policyPASS64713entries/2481696791bytes; no full verification or finite target K. Five
old untracked RLP files retained. Account10%weekly/0resetcredits/ordinaryallowed.
Push each commit. Next retain actual payload continuation/metadata and derive
payload argument/length, fresh payload record and actual gas load. Scratch
covered-outcome classification and global target composition remain open.
Overall40%, plausible30–50%.

## Actual fresh stateless record and copied bytes at the request guard

AllocationFrontier inverts the actual scoped allocation: the returned value is
the current heap pointer, its natural request room derives from observed return,
and the real caller state equals the current allocator post-state plus that
binding. No future room, stored value, successful mapping or output-state premise
is assumed. RequestCut reconstructs the literal six actions after the outer SSZ
validator: two offset loads, alloc96, chain-ID store, np and nlen declarations.
It exposes the real live lexical state/continuation and original nonlocal frame.
The si binding remains the observed allocation's old cursor; it is aligned and
has room for all96bytes above the incoming lower frontier.

InputImageFrame.of_words transports byte images using only their physical
backing-word frames. Its observed scalar-operation store theorem derives the
actual scalar read/mapping from continuation, and preserves copied input from
natural destination separation. RequestCut applies it to the real chain-ID store
at record+88, after deriving the record frontier and allocation state. Both local
setup declarations retain that image. RecordEntry joins this to the main-derived
stateless run: actual request guard entry, exact original input bytes, current
code/domain/endian/exception metadata, ssz_offs2701132528, bounded/aligned next heap,
and aligned96-byte si record beyond inputpointer+encodedlength+8. No claim is made
that the remaining request decoder has valid fields or preserves the image yet.

GuardActual removes a caller-supplied minimum clock from generic real decoder
rejection inversion. Checked clock extension excludes rejection on an observed
return; its passing continuation uses the original state/clock. RequestProgram
now uses actual Software decoder syntax and imports HeaderProgram directly;
RequestFromHeader explicitly imports its used HeaderFirstContainer theorem.
That older full request bridge is not revalidated at this checkpoint.

Validation: current-record-entry-v1.log PASS1233jobs/permitted printed axioms,
4.74s/MaxRSS1850840KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Roots include
RecordEntry and GuardActual. Components current-allocation-frontier-v1 PASS373,
current-request-record-cut-v2 PASS1228 and record-image-v6 PASS1232. Failed
diagnostics unindexed. Index7907historical/currentmodules/15703facts,
346current-reference modules; replacementclosure0/frozenmainunchanged. Incremental
policyPASS64711entries/2481684464bytes; no complete verification or global target K.
Account10%weekly/0resetcredits/ordinaryallowed; five old untracked RLP files retained.
Push every commit. Next derive actual np/nlen, passing request-length guard and
request offset44, then payload/gas and remaining copied-image lifetimes. Scratch
classification/global quantitative target composition remain open. Estimate40%,
plausible30–50%.

## Actual canonical first-container header and input-image dependency cleanup

HeapInput is now independent of the historical BlobBytes execute proof. The old
execution wrapper imports/reexports the unchanged definition. ScalarProgram and
HeapFrame consume the small definition directly. AllocatedArena splits the basic
arena/alignment/mapping facts from CopyContext; AllocatedBytes reexports it before
its historical copy_mapped theorem. That copy/zero execution closure is not claimed
revalidated. HeapFrame imports StoreWord explicitly. OffsetsValidStep/FaultStep
now explicitly import their generic declaration and binding rules after earlier
cleanup removed their transitive imports. Actual header syntax is retargeted to
Guest.Software.guestFn_decode_stateless_input. Framing.le32_lt bounds raw list
bytes directly; HeaderGuard no longer uses stale HostGas host-backing equations.
[Cleanup manifest](current-input-image-cleanup-20261027.json): HeapFrame82to29,
ScalarProgram51to12, HeaderEntryNormal114to65and HeaderAfterNormal111to62Solver
modules, compared with3df4e973d. All frozen implementation bytes remain unchanged.

CopiedHeap derives the actual post-copy frontier≥inputpointer+encodedlength+8,
using observed allocation room and current rounding arithmetic. SeparatedInput
retains that frontier and pointer alignment at the true stateless body entry.
CanonicalHeader derives schema21/1, encodedlength≥18, first offset=16and witness
offset between16and encodedlength−2 from real decoder return. No offset/schema
hypothesis or future helper success is supplied by the caller. A checked four-
clock extension funds the reusable header inversion; its natural conclusions
then apply to the original mathematical input. HeaderAfterTrace additionally
extracts the real unpadded continuing prefix: paid≤4and paid≤originalclock,
actual first-container continuation, and copied bytes intact through the first
two real workspace stores and validator. It uses the actual non-timeout enclosing
run to derive its precise funding. This does not yet derive the request/payload
second canonical offset or retain bytes through all subsequent decoder writes.

Validation: current-canonical-header-v7.log PASS1224jobs/permitted printed axioms,
7.52s/MaxRSS1853748KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Component
current-header-image-cleanup-v4 and canonical-header-v2 passed. Diagnostics v3/v4/v6
were stopped by the memory guard; v5 localized the kernel reduction issue. The
successful trace factors the prefix equality and input-image field transport;
no resource limit was increased. Failed/guarded logs are not indexed. Index7902
historical/currentmodules/15691facts,337current-reference modules; inventory7938,
replacementclosure0/frozenmainunchanged; incremental policyPASS64706entries/
2481661563bytes. No full verification or global K. Account10%weekly/0resetcredits/
ordinaryallowed. Five old untracked RLP files retained. Push each commit.

Next carry the actual allocator frontier and byte frame through the fresh96-byte
stateless record and its gas store, then derive request offsets (including44),
payload layouts and actual gas. Preserve all covered failure alternatives. Scratch
covered-outcome classification and global current-program quantitative/target
composition remain open. Overall estimate40%, plausible30–50%.

## Actual startup heap ordering and whole-main input separation

NormalHeapEffects/Loop/Call/Prefix retain a lower heap frontier only on real
resuming outcomes. AllocationRequest derives the actual request scalar from
an observed allocator return and its checked guard, then derives no-wrap room
and next-cursor order. No future allocation success, readable memory or room is
assumed. HeapMonotone checks the26-helper actual startup closure; source AST and
generated proof hashes are in current-startup-heap-generation.json.

EvmHeap treats the real mark/release explicitly. CallPrefixKey derives the saved
local mark through the literal prefix; CallPrefixFrameTrace recovers live scopes
from actual returned execution. EvmHeapProgram checks the35actions before the
release (including33literal byte stores). HeapMarks derives the exact real
snapshot and checks the actual release call; EvmHeapBounds proves the intervening
and remaining effects. Release is not assumed monotone: its real saved mark
restores the incoming lower frontier. Exceptional outcomes have no fabricated
heap effect. StartupHeap now retains2701134640after first SSZ through the actual
remaining startup calls, main setup and decoder precheck.

StatelessEntry retains the observed before-copy heap cell and proves all other
globals survive actual precheck/copy/tail entry. SeparatedInput reaches the real
stateless decoder from whole source termination with ssz_offs=2701132528,
input pointer≥2701134640and pointer+encodedlength+8≤2952790016. Every offset of
the64-byte workspace is strictly below the input. Mathematical input lengths
remain unrestricted, including lengths≥2^64. Startup/decoder stopped paths and
their full nonlocal observations remain explicit alternatives. This is entry
geometry; preserving copied bytes through actual decoder writes remains open.

Cleanup: HeapScope drops stale RLP U256MinCall dependencies, Solver closure151to9,
and uses current Software mark/release bodies. NoReturnScoped reuses the common
ignored-call theorem to avoid duplicate declarations when closures join. Exact
old imports/new hashes are in current-heap-cleanup-20261027.json. No guest source,
semantics, ROM, fixed proofs, Solution or claim bytes changed.

Validation: current-separated-input-v1.log PASS1166jobs/permitted printed axioms,
4.64s/MaxRSS1853380KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Roots include
SeparatedInput and NoReturnScoped; MainCopiedInput regression is in that closure.
Components: current-heap-base-allocation-v1, current-heap-call-marks-v1,
current-startup-heap-trace-v1, current-evm-heap-return-v2,
current-startup-heap-lower-v2 and current-stateless-heap-frame-v2 all passed.
Only the final successful unchanged-source closure is indexed; failed diagnostics
are not proof evidence. Index7898historical/currentmodules/15683facts,
298current-reference modules; inventory7933/replacementclosure0/fixedmainunchanged;
incremental policyPASS64701entries/2481645727bytes. No whole verification or K.

Next prove copied-image frames for real workspace/decoder stores, then close the
actual offset/layout/gas joins. Scratch covered-outcome classification, remaining
current crypto/maps and global weighted target composition remain open. Overall
estimate40%, plausible30–50%; no finite uniform target K. Five old untracked RLP
files retained. Account9%weeklyused/0resetcredits/ordinaryallowed. Push eachcommit.

## Actual first SSZ workspace and later-startup pointer preservation

Global allocation execution/normal/expected APIs and ProgramPrefix now use the
actual2952790016ceiling. RoundedExpected splits the reusable arithmetic lemma
from AllocationExpected's lexical prefix import; ProgramPrefix drops unused
ZeroCall. [Cleanup manifest](current-initializer-cleanup-20261027.json) records
exact prior imports at f762ad605 and current source hashes: GlobalNormal Solver
closure66to23, GlobalExecution56to17, Expected50to13, ProgramPrefix49to11 and
InitializerAllocations82to43. Existing literal initializer execution interfaces
are retargeted; remaining old Local helpers/callers are not silently revalidated.

InitializerNormal.prefix_return exposes every actual global allocation before
an observed initializer return. normal_prefix derives each real allocation's
room/funding and exact current state, plus the aggregate bound and clock, without
a future successful allocation or aggregate room/clock premise. Literal action
validity and word-sized numeric requests are checked static syntax facts.

EarlyWorkspace checks current SHA's64+128allocations, Keccak's192+200+136,
and first SSZ initialization's32+64+2048. Real zero_hashes=0 excludes the SSZ
initializer's early return. Keccak/SSZ literal stores preserve all globals on
every outcome, including failed stores; no future readability is supplied.
EarlyWorkspaceCalls derives real returned bodies/caller restoration from actual
continuing ignored calls. First_three/main_first_three connect these to the
literal first3main startup calls and declaration-derived heap/scalars/zero flag.
After SSZ, heap=sourceBase+2864=2701134640; the64-byte ssz_offs allocation is
sourceBase+752=2701132528=0xa10002f0. This replaces the old accelerated program's
unrelated2713715344literal; no frozen guest bytes were changed.

OffsetsFrame checks all-outcome ssz_offs global preservation for the closed43-
helper graph used by later10startup roots and decoder/result/output helpers.
[Generator/manifest](current-offsets-frame-generation.json) record all source
proof inputs/hashes; Lean validates every literal inequality and actual callee.
WorkspacePointer joins it to the real remaining startup sequence: main_offsets
proves the actual post-startup cursor cell, retaining arbitrary mathematical
input lists and actual early-stop alternatives in the existing whole-main cut.
This proves global pointer preservation only. It does not prove that workspace
contents are unchanged, that input cannot overlap it, or a startup runtime bound.

Validation: current-workspace-pointer-v1.log PASS1146jobs/permitted printed axioms,
3.45s/MaxRSS1451372KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Combined
roots include WorkspacePointer, existing MainCopiedInput and NormalExpected,
so both allocation API retargeting and the previous whole input bridge pass.
Components: global-allocation-api-v1 PASS282, initializer-normal-prefix-v1 PASS290,
early-workspace-reached-v1 PASS366, offsets-frame-v1 PASS270. Failed diagnostics
unindexed. Generation inputs/current source hashes match. Index7884historical-or-
current modules/15607facts,279current-reference modules; inventory7919/replacement
closure0/frozenmain unchanged; incremental policy PASS64687entries/2481410152bytes.
No full fixed-policy/axiom audit/comparator verification or uniform K claimed.

Next preserve a lower persistent allocation frontier through the remaining
startup helpers, treating evm_init's real saved heap mark/release explicitly.
Then relate the actual input pointer to the64-byte SSZ workspace, derive its
protection through copying/decoder writes and finish offset/layout/gas joins.
Do not infer memory ownership from a preserved global pointer. Current local
scratch NoReturn results still need genuine covered-outcome classification;
global quantitative/target composition remains open. Overall estimate40%, range
30–50%; no finite uniform target K. Five untracked pre-rebase RLP files preserved.
Account8%weeklyused/0resetcredits/ordinary allowed. Push every commit to georg.

## Complete main-to-copied-input/stateless-entry bridge

ReadHostEffects proves host-byte equality on every outcome under the real
source oracle. Its generic read reply/wrapper proof covers arbitrary widths,
absent backing and returned-length checks. Calls, loops, branches and lexical
scopes compose using actual code/oracle invariants; event histories are allowed
to change. Unlike normal-return startup host frames, this read-only interface
also covers exceptions and terminal read failures. PrecheckHostFrame checks
all5actual precheck helpers, generated from checked fixed-syntax proof terms;
[manifest](current-precheck-host-generation.json) records every input/hash.

The generated global frames for ssz_fail/host_input_byte/host_input_le32/
ssz_check_offsets/precheck_host_ssz_header now share any_key proofs, retaining
old cursor-specific wrappers. This proves actual heap_ptr preservation through
the precheck without assuming a future successful read, valid schema or stable
ordinary memory. Its actual workspace writes are not erased from execution.
TailCallNormal now imports Guest.Model explicitly after earlier dependency cleanup.

DecoderInput reconstructs the literal decode_host_input body and joins its real
precheck/input_blob calls. Every actual precheck outcome preserves host bytes,
heap and arenas. A real returning decoder exposes the completed precheck and
copy, derived encoded-length bound, exact copied tuple/image and real tail-call
continuation/restoration. Blob.call_reached now also returns its actual
CallPrefix.Reaches action; downstream metadata comes from that trace instead of
an assumed caller state or byte-order field missing from Copied.

StatelessEntry checks the real installed Software decoder, actual tuple argument
reads and real p/len callee bindings. It transports copied bytes into that actual
callee and derives the bounded aligned next allocation frontier from the true
copy heap update. MainCopiedInput joins this to complete source termination:
startup stops and actual decoder/handler stops remain explicit, while a completed
prefix supplies the real stateless run and main's actual si binding. No future
successful helper, supplied schema/layout/gas, mathematical input-length ceiling
or extra post_not_timeOut premise is introduced. This reaches the stateless
entry only; image lifetime through later workspace writes is not yet proved.

EvaluationFields adds unconditional shared-domain/base preservation from the
trusted evaluator invariant. CallPrefix Reaches/Execution retain both fields.
HostState now carries installed exception declarations, the true shared domain
and actual source base through main/startup/setup/copy/tail entry, alongside its
arenas/domain/code/little-endian/oracle/host fields. No fixed source/semantics/
ROM/Proofs/Solution/claim changes were made.

Validation: current-main-copied-input-v2.log PASS1131jobs/permitted printed axioms,
231.79s/MaxRSS5367852KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Components:
precheck-host-frame-v2 PASS219, decoder-input-image-v2/v3 PASS1128 and whole-main
copied-input-v1 PASS1131 before the extra layout fields. Failed diagnostics
unindexed. All generated source/input hashes match reports. Index7877historical-
or-current modules/15535facts,264current-reference modules; inventory7912modules,
replacement closure0/fixedmain unchanged; incremental policy PASS64680entries/
2481116195bytes. No full fixed-policy/axiom audit/comparator replay claimed.

At that checkpoint the workspace address was pending; the later checkpoint
above now derives its actual64-byte allocation and pointer transport. Persistent
heap ordering relative to the later copied input remains open. A bounded aligned
heap cell alone does not prove nonaliasing, so do not transport the entry byte
image through header workspace stores without that separation. Then actual
decoder offsets/layouts/gas, genuine scratch covered-outcome classification and
remaining global quantitative/target obligations. Overall estimate40%, plausible
30–50%; no uniform finite target K yet. Five old untracked RLP files retained.
Account8%weeklyused/0resetcredits/ordinary allowed. Push each commit to georg.

## Actual normal startup host frame and bootstrapped decoder heap cursor

NormalHostEffects proves conditional host preservation for resuming outcomes:
normal fallthrough, return, break and continue. Terminal/error/exception/timeout
paths have no host-frame assertion. NormalHostCall composes ordinary tail,
ignored, local/global assigned and lexical scoped calls using the host state at
their real returned bodies; NormalHostLoop handles actual loop control. No
future helper success, allocation room, readable buffer or canonical oracle is
assumed by these generic host rules.

CurrentStartup/NormalHost checks real normal-return host frames for the closed
28-helper startup graph. The trap_with case uses actual Trap.never_returns and
is vacuous only for a real normal return; it does not assert that trapping output
writes preserve host memory. [Generator/report](current-startup-normal-host-generation.json)
record the fixed Software source hash, graph and generated source hash; Lean,
not the scanner, validates the proofs. HostPrefix joins the actual13startup
commands and genuine5-action setup to original host memory, current arenas,
little endian and source oracle. reached_host retains complete source observation
and startup stops. decoder_entry_data derives these fields at the actual returned
decode_host_input entry from its real completed lexical trace.

AllocationChecked.rounded_aligned_word proves literal alignment even if the
preceding word addition wraps. checked_post_of_normal derives both real guard
passes and exact post-state from an observed allocator return without an initial
heap-end/no-wrap premise. reached_cursor also derives the incoming scalar heap
cell from its genuine declaration read; it supplies a bounded aligned post-cursor
without assuming either old or future cells. Natural room and monotonicity are
not asserted under arbitrary incoming cursors. Existing bounded-entry room proof
remains separate and unchanged.

AllocationCursor lifts this result to an actual scalar allocation action using
real installed alloc/trap entries and actual unary request binding. DecoderHeap
uses main's second setup allocation, then transports its bounded aligned cursor
through genuine memzero/si/err_code actions. Thus exact startup allocation totals
are unnecessary for this input-entry invariant. decoder_entry_heap joins all
host, oracle, endian, arena and heap prerequisites at the real decoder body entry.
Internal precheck/input_blob transport and copied-image lifetime remain open.

Memzero.any_key generalizes its generated all-outcome global frame to any selected
key; the existing arena-specific API is retained as a wrapper. Its generator and
manifest now reproduce that shared proof rather than duplicating it for heap_ptr.
No fixed source/semantics/ROM/Proofs/Solution/claim bytes were changed.

Validation: current-decoder-entry-heap-v1.log PASS372jobs/permitted printed axioms,
3.49s/MaxRSS1451084KiB;8GiBwhole-hostguard/twoslots/artifactcachefalse. Components:
startup-normal-host-v1 PASS213, startup-host-prefix-v4 PASS359, allocation-checked-v2
PASS136, allocation-cursor-v2 PASS371. Failed diagnostics unindexed. All generated
source hashes match their reports. Index7869historical-or-current modules/15490facts,
255current-reference modules; inventory7904/replacement closure0/frozen main unchanged;
incremental policy 64,672 entries /2,481,059,647 bytes. No full verification claimed.

At that checkpoint the internal precheck/input_blob/stateless-entry join was
pending; the later checkpoint above now supplies it. Workspace geometry/image
lifetime and canonical offset/gas joins remain open. Then covered scratch
classification and remaining global quantitative/target obligations. Normal host
frames say nothing about terminal startup budgets or covered FFI classifications.
Overall estimate remains40%, plausible30–50%; no uniform finite target K yet.
Five unfinished pre-rebase RLP files preserved/untracked/unclaimed. Account7%
weeklyused/0resetcredits/ordinary allowed. Push every commit to georg.

## Post-rebase dependency cleanup and genuine lexical decoder cut

CallPrefix now imports LocalEffects instead of the unrelated ClockCostScopeLocals
umbrella. Its transitive Solver dependency closure falls155to7modules; Execution
157to9, Trace158to10 and Globals159to11. CaughtAssignedStops drops unused
AssignedCallData (9to6), while NoFallthrough states Guest.Model explicitly and
drops unused CallResume (7to5). All before counts use exact pre-cleanup imports
at f52bea987. [Cleanup manifest](rebase-prefix-cleanup-20261027.json) records the
method, removed dependencies and retained source hashes. No fixed guest bytes,
semantics, source ROM, Proofs, Solution or claim changed.

CallPrefix.cutAt/reconstructAt retain exact lexical syntax even for repeated
calls to alloc. Observe retains outcome, clock and LocalEffects.erase (all state
except locals/clock); StoppedFrame and actual action/list classification now
preserve this nonlocal observation on every stopped path. Existing clock-only
Stopped/classify/priced_trace interfaces remain available as projections.
Execution.split/singleton expose genuine subtraces without reevaluation or local
scope restoration. No supplied future successful action or clock is required.

CurrentStartup/DecoderPrefix cuts the literal6actions after13startup calls:
out allocation, z32 allocation, memzero, si declaration, err_code declaration,
and the caught decode_host_input call. Its real error handler preserves both
arena cursors through serialization/byte-store/output/terminal halt. Reached
continuations retain live lexical bindings; stopped prefixes retain actual
memory/globals/FFI/clock/result, with both arenas and domain/code preserved.
reached joins this to the actual complete source observation for arbitrary input
lists, including stopped startup and decoder paths. This is control/frame
transport, not a global runtime or initializer cost bound.

DecoderReturn proves the literal rejection handler cannot fall through. The
real normal assigned caught call must therefore have received an actual checked
scalar decode_host_input return, paid its caller clock and bound si in the real
caller locals. reached_return extracts that call from the genuine six-action
trace; an exception handler is not substituted for a successful decoder.

Validation: current-decoder-return-v5.log PASS354jobs/permitted printed axioms,
3.88s/MaxRSS1476300KiB,8GiBwhole-hostguard/twoslots/artifactcachefalse. Earlier
current-decoder-prefix-v4 PASS350jobs/5.20s/MaxRSS1590132KiB and cleaned generic
prefix-frame-v2 PASS125jobs. Failed diagnostics unindexed. Index7861historical-
or-current modules/15426facts;245current-reference modules. Inventory7896modules,
replacement closure0/fixedlatestmain unchanged. Incremental policy
PASS64664entries/2480839957bytes. No full policy/axiom audit/comparator replay claimed.

At that checkpoint, normal startup host/heap facts were still pending; the
later checkpoint above now supplies the decoder entry prerequisites. Internal
precheck/input_blob/copy-image/decode_stateless_input lifetime joins and genuine
scratch covered-outcome classification remain open. Conditional arena preservation or NoReturn still
does not discharge whole-path exclusion or a uniform finite target K.
Overall effort remains40%, plausible30–50%; no global finite target bound yet.
Five unfinished pre-rebase RLP files preserved/untracked/unclaimed. Account7%
weeklyused/0resetcredits/ordinary allowed. Push every commit to georg.

## Actual startup cut and all-outcome arena-global preservation

CurrentStartup/Code checks real Software entries for a closed46-helper graph:
all13startup roots, decode_host_input, serialize_result and output_write with
their actual callees. The graph is acyclic; its preservation proofs use actual
installed code rather than the scanner as evidence. Every helper outcome
preserves both scratch_ptr and frame_mem_ptr, including malformed arguments,
failed reads/stores/shapes, exceptions, terminal FFI and timeout. This supplies
no iteration count, runtime bound, successful helper trace or mapped buffer.

GlobalEffectsGlobalCall proves the missing generic case of calls assigning a
different global; GlobalEffects.shared_load handles all actual local shared-load
outcomes. GlobalEffectsLoop states its Nat induction import explicitly. The
generator emits checked compositional proofs from actual Software syntax and
records the source/hash/call closure and generated source hashes; Python output
alone is not validation. Both arena keys remain untouched even when startup
calls fail or change memory/FFI/other globals.

CurrentStartup/Prefix reconstructs the literal13commands after real mem_init.
append_execution is an exact all-clock evaluation identity, retaining stopped
prefix outcomes/states and resuming only after real fallthrough. prefix_state
transfers both initialized cursor cells, source domain and installed code.
split_execution/reached join this to Main.reached_memory for arbitrary actual
terminating source inputs, preserving the exact observation: either startup
actually stops or its genuine following main state has ArenaState. No future
initializer completion or input size/validity premise is supplied.

Validation: current-startup-decoder-globals-v1.log PASS343jobs/permitted printed
axioms;72.90s/MaxRSS1536032KiB, same8GiBwhole-hostguard/twoslots/artifactcachefalse.
Earlier current-global-call-frame-v1 PASS266jobs, startup-globals-small-v1 PASS272,
startup-globals-all-v1 PASS297. Failed startup-prefix diagnostic unindexed.
Index7859historical-or-current modules/15404facts,235current-reference modules;
inventory7894/replacement closure0/fixedlatestmain unchanged; incremental policy
PASS64662entries/2480817587bytes. No fresh full fixed-policy/axiom audit/comparator
replay, initializer quantitative budget or finite global K claimed.

At that checkpoint, the lexical decoder cut and stopped-path nonlocal frame
were still pending; the later checkpoint above now supplies them. Normal startup
host/heap frontier and internal decoder input-image joins remain open, followed
by actual scratch cursor transport/covered terminal-outcome classification;
NoReturn alone does not discharge global covered paths or the target bound.
Five unfinished pre-rebase RLP files remain preserved/untracked/unclaimed.
Account6%weeklyused/0resetcredits/ordinary allowed. Push each commit to georg.

## Actual scratch clears/constructors and genuine main initialization

ZeroProgram now names the real Software memzero. ZeroUnmapped proves its first
32-byte loop stops at timeout or the first unmapped ordinary store, then follows
the actual aligned branch and i scope to rule out any body return. ZeroUnmappedCall
installs actual function12 and rules out a normal ignored memzero continuation.
No future mapped buffer/readability or oracle result is supplied.

ScratchClear installs actual allocator8, derives room from its real return,
derives rounded pointer≤current bounded scratch cursor and alignment, reconstructs
the genuine caller continuation and invokes the actual failed clear. Source clock
and allocator failure paths require no future completion premise. ScratchConstructors
matches current msg_new_scratch function422, proves its body and a real scoped
caller cannot return under current ordered/bounded arena cursors and domain.
ScratchFrame matches current frame_new423 and both real marks6/9; it carries the
same cursor facts through both exact snapshots to the actual280-byte allocation/
clear and rules out a body return, without requiring a message read or mapped
fresh frame. This remains conditional local control evidence: it does not yet
classify all terminal outcomes as uncovered or establish whole-program EVM
unreachability. Actual earlier startup/decoder arena preservation remains open.

MainProgram/MainEntry/MainMemoryPrefix now follow current Software main812 and
mem_init1. The genuine declaration pass proves67scalar globals (rather than old93),
and sha_names no longer asserts the removed sha_accel global. Entry.base is derived
from the real declaration frame. mem_init sets heap_ptr=@base, scratch_ptr=2701127680,
frame_mem_ptr=2688618496. Every actual source termination reaches the computed
memory prefix with its genuine initialized globals and literal remaining main
execution. The old accelerated startup-prefix modules still require migration;
this check does not revalidate them. SourceEntry, exception installation and actual
declaration-global facts rechecked through these current roots.

Cleanup: PureReturn states its CodeEnvironment/Model imports explicitly; ZeroEnvironment
uses syntax/ABI rather than whole ZeroMemory; ZeroCall imports its memory proof
explicitly. Actual arena allocator/mark syntax and remaining zero-loop shapes are
retargeted to Software. Existing conditional mapped memzero caller rechecked.

Validation: current-main-memory-prefix-v1.log PASS708jobs/permitted printed axioms,
8.72s/MaxRSS1353688KiB,8GiBwhole-hostguard/twoslots/artifactcachefalse. Components:
current-main-entry-v1 PASS707, current-scratch-frame-v2 PASS694, current-scratch-message-v1
PASS692, current-scratch-clear-v3 PASS691, current-zero-unmapped-v4 PASS661. Failed
diagnostics unindexed. Index7809historical-or-current modules/15346facts,
179current-reference modules; inventory7843/replacement closure0/fixedlatestmain
unchanged; incremental policy PASS64610entries/2480511183bytes. No full verification.
Next actual startup/decoder arena preservation, scratch outcome classification,
current heap/input-to-decoder lifetime and canonical offset/gas joins, then all
remaining quantitative/target obligations. Keep the full finite-bound objective;
no conditional NoReturn theorem substitutes for a uniform target K.
Five unfinished RLP files preserved/untracked/unclaimed; account5%used/0reset credits.

## Complete actual input body/caller and current allocation room

AllocationArithmetic, AllocationNormal, AllocationCall and AllocationCallNormal
now use the real2952790016guest ceiling. A normal allocator return derives room
from the actual passing guard and the current heap-end invariant; replay then
identifies the true returned pointer and exact heap-global update. NormalCallClock
uses core case analysis and imports only the generic call interface.

BlobReached.after_guard_reached joins that actual allocation to the checked
copy tail. body_reached additionally inverts the real len declaration, successful
host length read and passing guard. For arbitrary mathematical input lists it
derives encodedLength≤1073741808, pointer+encodedLength+8≤2952790016, the exact
returned pair, copied byte view, exact heap globals, ceil(encodedLength/8)+1
paid body ticks, code/domain/host/oracle preservation and the protected-word
frame. call_reached derives the genuine callee return from an actual returning
caller, restores caller locals, installs the true tuple at its destination and
reaches its actual continuation, with the extra caller tick explicit. No room,
read/store success, returned helper result or completed copy is an entry premise.
Current initial heap cursor≤cap, pointer alignment, endian, installed code and
host/oracle facts remain to be derived from actual main at this boundary.

CurrentDomain.ordinary_lower proves the actual compiler installation domain has
no addresses below sourceBase, including wraparound exclusion at its real cell
count. scratch_unmapped and store_below_base_error prove a real scalar store
there fails immediately. This does not yet prove whole-program unreachability;
next check genuine scratch allocator/clear callers and propagation to covered
outcomes before extending old EVM/map/crypto proof families unnecessarily.

Validation: current-input-entry-domain-v1.log PASS1032jobs/permitted printed axioms,
3.64s/MaxRSS1310368KiB, same8GiBwhole-hostguard/twoslots/artifactcachefalse.
Component current-allocation-normal-v2 PASS116jobs and current-blob-reached-v5
PASS1031jobs; failed diagnostics unindexed. Index7804historical-or-current modules/
15329facts,146current-reference modules; inventory7838/replacement closure0/fixed
latest-main unchanged; incremental policy PASS64605entries/2480485979bytes.
No fresh fixed-source policy/axiom audit, full verifier or finite global K.
Extended Expected/Global/Local allocator APIs retain old assumptions and still
need migration; do not treat their historical checks as current success.
Five unfinished RLP files preserved/untracked/unclaimed; account5%weeklyused,
zero reset credits/ordinary allowed. Continue autonomously and push every commit.

## Actual copy bytes, returned tuple and length read

CopyStepReached inverts the real shared-read/store/increment sequence, deriving
the destination mapping, all eight present host bytes and exact wordPost.
CopyLoopReached follows the actual finite evaluator, excludes body break/continue,
derives the exact repeated state and every observed read/store, and requires no
future presence, mappings, completed helper trace or clock funding.

CopyObservedBytes derives InputBytes and the exact frame outside copied words
from that actual normal loop. Actual raw-list bytes (including padding) come from
observed current-host presence. Domains/endian/host/oracle/globals/code survive;
clock falls by exactly ceil(length/8). Pointer alignment/no-wrap, the bounded
current scalar length and actual p/i/len/w bindings remain caller entry facts.
CopyTailReached joins the real i/w lexical scopes, loop, tuple return and scope
restorations: its actual returned value is exactly the pointer/length pair, with
the complete byte/frame facts retained.

HostLengthCurrent derives length-header presence from actual normal reads and
identifies the real scalar as the low64bits of input.length. No mathematical
list-size bound, backing extent or future mapping premise is introduced.
CurrentHostRead.present_bytes factors the corresponding observed-data lemma.
CopyStep no longer imports stale HostWords; CopyMemory imports only CopyState;
pure walk state/frame lemmas moved into CopyWalkState with public names retained.
CopyWalk's explicit current maximum is corrected to134217726iterations.

Validation: current-copy-tail-reached-v1.log PASS1025jobs/permitted printed axioms;
6.18s/MaxRSS1777696KiB, same8GiBhostguard/twoslots/artifactcachefalse. Component
successes: current-copy-loop-reached-v2 PASS667jobs, current-copy-observed-bytes-v3
PASS1021jobs, current-host-length-reached-v1 PASS1022jobs. Failed diagnostics
unindexed. Index7802historical-or-current modules/15321facts,139current-reference
modules; inventory7836/replacement closure0/fixed latest-main unchanged; incremental
policy PASS64603entries/2480471113bytes. No full verifier/finite global K claimed.

Next: real initial allocator/caller-to-copy-tail geometry and decoder lifetime;
AllocationArithmetic/AllocationNormal still contain old33806089496ceiling and
must use current2952790016heap-end invariant. Check earliest scratch accesses and
their real source covered-outcome consequences before large map/crypto migration.
Then actual canonical offsets/gas and remaining global/weighted-target obligations.
Five unfinished RLP files remain preserved/untracked/unclaimed; account4%used.

## Current input-copy cost and dependency cleanup

BlobCurrentCost bounds every actual input_blob body outcome by 134,217,728
source call/loop ticks, every caller by 134,217,729. It derives the scalar length
from the actual continuing shared load and length ≤1,073,741,808 from the real
passing guard. No validity, readable future byte, allocation room, successful
store or supplied completed trace is a premise.

CounterStrideCost.unsigned_stride_cost proves the actual unsigned loop rank
(length + stride - 1 - current)/stride. The last stride may overshoot. Real
continuations derive the increment without wrap and preserve the limit.
BlobCopyCost instantiates stride eight/body cost zero; failed reads/stores are
included. Source clocks omit straight-line target work.

Cleanup:

- BlobProgram uses Software AST/current guard/generic state helpers, dropping
  obsolete HostLength. BlobCallEnvironment uses syntax/code interfaces instead
  of BlobExecute and the arithmetic umbrella; actual current entry24.
- PersistentAlloc uses Software AST/binding/declaration helpers instead of
  Copy32Execution. AllocationCost drops unrelated Arenas.Cost for its real clock/
  trap tools; actual entry2. TrapNoReturn/TrapCost use Software entry0 and the
  thin OriginalEntry catalogue instead of the old guest/arithmetic environment.
- Fixed counter increments moved from byte-store code into CounterFlow; shared
  local-summary sequence composition moved out of shared-store code. Public
  names retained. SharedLoadLocal derives actual scalar destination words and
  other-local preservation. Two guard-cost proofs use explicit core Nat
  transitivity instead of borrowing imports from an unrelated umbrella.
- Old task/progress documents are archived exactly, with hashes; active plan
  separates current work from superseded designs and operational constraints.

[Dependency cleanup manifest](rebase-code-cleanup-20261027.json): transitive
Solver imports fall from245to10 for BlobCallEnvironment,246to23 for TrapCost,
29to6 for PersistentAlloc and255to31 for AllocationCost. These are dependency
counts, not runtime measurements. Every changed proof-source hash matches the
successful build index.

Validation: current-blob-body-cost-v3.log **PASS304jobs**, permitted printed axioms,
5.36s, MaxRSS1,441,208KiB. Targets BlobCurrentCost, TrapStopped, ByteStoreLocal,
HostPrecheckCost; one two-slot build, artifactcachefalse, 8GiB whole-host guard.
Earlier current-blob-copy-cost-v3.log PASS213jobs. Failed diagnostics unindexed;
later whole-body success supersedes allocation/shared-load diagnostic failures.

Index7796historical-or-current modules/15310facts;123current-reference modules.
Inventory7830modules/replacement AST reverse closure0/frozen latest-main unchanged.
Incremental Solver/package policy PASS64597entries/2480443432bytes. This is not
a fresh fixed-source policy/axiom audit or comparator replay.

Next: actual successful-copy byte contents/frame/lifetime; port stale HostLength/
HostWords/HostGas callers to observed reads; actual offset/gas joins and current
main/heap/scratch invariants. Then Patricia maps/software crypto, serializer/root/
EVM/global totals, current compiler/weighted target composition, finite K and
final cleanup/applicable validation. Overall effort40%, range30–50%.
Five unfinished pre-rebase RLP files preserved/untracked/unclaimed. Account4%used,
zero reset credits, ordinary usage allowed. Push every commit to georg.

## Earlier current-reference checkpoints

| Commit | Checked result | Remaining limit |
| --- | --- | --- |
| 587d4a239 | Genuine current main/mem_init prefix; conditional current scratch constructors cannot return. | Later arena transport and covered-outcome classification still needed at that checkpoint. |
| ca9b24dc2 | Actual full input body/caller copied image and allocator room; current domain excludes scratch. | Main initialization and genuine scratch callers still needed at that checkpoint. |
| b0ca826ff | Actual loop/suffix copied bytes and protected frame; real length read with arbitrary list sizes. | Whole allocator/input-body/caller join still needed at that checkpoint. |
| 418e447ec | Whole current input-copy all-outcome source cost; stale dependencies removed and history separated from active plan. | Copy contents/caller reachability still needed at that checkpoint. |
| 44d188c1b | Whole current header precheck ≤85body/86caller source ticks; actual signed small-count offset loops. | Offset guard semantics/global target composition open. |
| ff66d97ab | Actual shared reads derive presence/bytes/scalar post-state; bounded gas word under canonical offsets. | Offsets need caller derivation. |
| 441ac0cb5 | Core Software installed-code environment;65closed stale generated modules removed. | Software migration incomplete. |
| 818e998a9 | 560commits rebased onto f892870c8;oldhead/RLPfiles preserved. | Historical checks need current revalidation. |

Complete older records: [progress history](PROGRESS-HISTORY-PRE-CLEANUP-20261027.md)
and [task history](BOUND-HISTORY-PRE-CLEANUP-20261027.md).
[Archive hashes](rebase-cleanup-history.json) establish exact preservation.
Old target indices/local contracts are not current whole-program progress
without checking their statements and dependencies.
