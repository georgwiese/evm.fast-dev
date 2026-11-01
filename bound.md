# Finite runtime bound for the current Pancake program

Prove an explicit uniform finite bound on **formal target evaluator steps** for
**the unchanged current implementation**, under the fixed challenge's gas and
covered-outcome assumptions. Keep the bound reasonably tight. **No numerical
ceiling applies.** Do not replace or optimize Pancake to meet a Yukon score
limit. A score-compatible claim or Yukon submission is not required.

Reference main: `6957805e26f4bb44ef756406a2bd14d56cf89b92`, including the mapped
scratch-domain update. Actual source: `Guest.Software.guestAst` in
`Guest/SoftwareAst.lean`. Preserve fixed source, semantics, ROM, baseline proofs
and pinned dependencies. **Do not read CLAUDE.md.** Fixed definitions govern
stale prose. Follow AGENTS.md and docs/CHALLENGE.md, docs/SUBMISSIONS.md and
docs/TESTING.md as needed.

## Completion criteria

- Follow `InitE.Certificate` in `InitE/Challenge.lean`: every mathematical input
  byte list with declared gas at most200000000, conditional on actual covered
  source termination. Derive validity, ownership, gas, allocation and helper-entry
  conditions from that execution. Do not assume future success or funding.
- Retain actual accepting output matching and covered rejection/trap cases.
- Prove a uniform target-step theorem and evaluate its bound exactly. Source
  call/loop clocks omit straight-line target work; an input-dependent finite
  halt witness at infinity is insufficient. Review dominant slack.
- Keep claim.json at infinity until an actual finite certificate justifies
  changing it. A K above Yukon's scoring range does not invalidate the task.
- Remove obsolete alternate implementation code and unused shortcuts after
  their dependencies have been replaced. Do not change the actual guest program.
- Selected Lean builds are not complete isolated verification, comparator
  export or kernel replay. Do not claim final verification without a successful
  run; existing restrictions on running the full verifier here remain in force.

## Current evidence — 2026-10-31

**No global finite target K or whole-main source allowance yet.** Claim infinity.
The previous55% effort estimate concerned old main `f892870c`; it is not a
validated estimate against6957805e. Module/fact counts do not measure effort.
Older early-stop arguments based on unmapped scratch do not apply here.

The checked actual main prefix reaches its first transaction-trie call within
1761211446598 source call/loop ticks, retaining the real decoded data and
continuation. Ranked witness materializer<=1757412483170; complete
state_init<=1757412483565 under its derived physical entry conditions;
main through complete state_init<=1760801932784. Later main is not connected.

The actual indexed setter and complete indexed loop retain a supplied pure
value property through key conversion, insertion, header store, counter advance
and lexical return. The real transaction decoder/entry derives pointer+length
<=inputEnd and, for nonempty values, pointer>=2701134824. Actual builder ABI,
setup and loop retain those facts as Values. Source allowances remain36826
per iteration and36827*count for the loop. The actual builder now retains
heap<=2952790016 and a nonhash kind for every nonzero root through setup and
the complete loop. Those observed facts now construct the actual serializer
Persistent/Root.Entry, with the original decoded-value interval, startup
Keccak environment and scratch cursors. No incoming persistent-cap or
nonhash-root hypothesis was added.

Complete current fill/node_rlp/node_hash/mpt_root body/caller costs and normal
frames are checked, including all three finish node kinds, real buffer sizing,
compact/value/reference copies, hash cache stores and caller restoration.
The fill proof derives its real48-byte scratch stack, registered original trie,
linked headers, prepared frames, current selection indices and traversal rank
<=521215. Every actual continuing step preserves its physical model and strictly
decreases that rank. Normal completion retains the sized original root cache,
restores the original scratch arena and protects the real original input band.
No empty-only root conclusion remains in CurrentTrieRoot.

Persistent physical entry requires nodes/paths between an aligned lower frontier
and the actual bounded aligned heap in2701131776..2952790016. Thus stored paths,
compact copies and new encodings fit the251658240-byte persistent window.
Borrowed value pointers/lengths have the genuine input interval above, with
inputEnd before the node frontier. The actual Keccak state/pad end before
2701134824, below the borrowed input band. The actual indexed builder now supplies these physical heap/layout and
graph/path facts from its own setup and insertion loop; no successful future
read is assumed.

node_rlp returns its real pointer/length pair with retained registered trie,
heap, scratch and input/global frame. node_hash handles both uncached encoding
and populated HASH24 fast paths, returning a genuine nonnull pointer and
bounded aligned heap while protecting input and every nonheap global.
mpt_root handles empty and nonempty tries, copies the actual32-byte digest and
returns zero while retaining that same frame. Its owned aligned output must
be below the protected input band or after it. Caller protectedEnd may be
earlier than serializer inputEnd; this accommodates later withdrawal output.
HeapScope.release_normal unconditionally restores the actual saved mark from
its normal call; it requires no mark<=currentheap premise.

The allocator now has a checked NormalHeapEffects.Returning contract for
arbitrary callee locals. Its real first guard forces a scalar request; actual
normal allocation then retains the incoming lower frontier and bounds/alignment
from its own guards. All four constructors, leaf/extension splitting and the
complete real insertion body preserve that bounded heap on resuming outcomes.
Unsecured key conversion additionally exposes actual request room and its
rounded heap<=2952790016 from the same call, without requiring that cap at
entry. Existing indexed rows already carry nonzero pointer and length, so
their setters use insertion. The actual Converted, setter Output and complete LoopModel now retain
heapUpper from those observed calls. Header construction exposes its real
16-byte room and supplies the initial cap even for an empty loop. The incoming
builder Entry still requires only ordinary heap ownership; no persistent-cap
hypothesis was added. Its full root-entry connection is checked.

The genuine insertion result now retains a nonhash root tag. Actual leaf/
extension constructors supply their literal tags; a returned branch retains
its already established nonzero tag. Every real dispatch output carries this
fact through scope restoration and parent/root stores. The complete insertion
loop proves the returned root's kind from its actual first slot=0 update,
without requiring an incoming nonhash root. The actual assigned caller,
indexed setter, key conversion and full indexed loop retain it. Root0 is
handled by the conditional invariant; no new entry hypothesis was introduced.
Thus heap, root kind, borrowed-value interval and stored-word cache bounds now
supply the real indexed/root producer connection.

The complete current indexed builder, including setup, all insertions, genuine
nonempty serialization, digest copy and heap release, has checked source cost
36827*count+Root.bodyPrice(2^64-1,valueLimit)+6. At count<=12582752 and
valueLimit<=268435456 this is91390403933770582; its real caller adds1.
Its actual normal return supplies zero, restores the saved entering heap,
retains every nonheap global and protects the chosen earlier input/header band.
Entry.widen derives larger borrowed frontiers/caps from numeric inequalities.
CurrentIndexedSetup's obsolete normal_count_zero and empty-only proofs have
been removed.

The actual transaction-trie caller now instantiates this complete allowance
from PhysicalHeader.transaction_entry_owned and the genuine startup environment.
The normal caller preserves its real PhysicalHeader for arbitrary transaction
count, including nonempty tries. The serializer input frontier is enlarged to
the actual entering heap; its protected band ends at header+248, before txr.
PhysicalHeader.of_heap_band retains decoded data, header cells, actual frontier
and caller locals while allowing earlier hash workspace changes. The complete
payload-header prefix through the transaction trie stops within91390404330701644
source ticks or reaches the actual withdrawal suffix with the same physical
inputs and continuation. No zero-transaction conclusion is used.

The actual withdrawal loop now retains InputValue(heap) for every encoded row.
The same real64-byte encoder allocation and <=57-byte result establish each
new interval; older intervals remain before the advancing heap. The completed
array supplies its actual indexed builder entry, including nonempty rows,
without any empty-count premise. Its trie caller costs
36827*count+Root.bodyPrice(2^64-1,64)+7; the root body at this value cap is
91210677590434782. At count<=335544 the caller costs91210689947513677; complete
withdrawal setup/encoding/trie suffix costs91210690015629111. Normal return
restores the real entering heap and protects the actual earlier input/header
band, ending at header+248 before wr. BeforeRequests no longer contains
transactionsZero or withdrawalsZero.

Both actual trie calls now compose through request encoding, request hashes,
and the final BAL hash. Complete unchanged payload_header body<=
182601094624356402 source ticks on every outcome, from its genuine decoded
Data and the earlier transaction scan. Its actual normal return retains the
real returned header, physical input/header facts and StateFrame through all
lexical restores. This whole helper is checked; connecting it and the nonempty
transaction execution to the complete actual main remains.

The actual run_attempt header caller is now checked in HeaderMainEntry. Its
normal AfterHeader retains the genuine hdr/pl bindings, decoded Data, owned
header fields, heap frontier and original state frame, with no zero-count
fields. Its real scoped header caller costs182601094624356403; the complete
run_attempt prefix through the header stops within182602855438871939 source
ticks or reaches the actual afterPayloadHeader continuation. The stronger
trace retains the genuine initialized workspace/block records before and
after header construction, and the observed pre-workspace stable memory.
This is the actual helper prefix from its decoded entry, not a whole-program
target bound. TransactionData's later version-check/VM clients remain stale
and have not been revalidated by this selected root.

Actual transaction field-reader prerequisites are now checked in
TransactionFields: tx_scalar_item, tx_bytes_item, tx_fixed_bytes, tx_to_item
and tx_list_item. Their real row cells derive the parser arguments; each
complete body costs60*rowLength+11 source ticks, including all rejecting and
stopped outcomes. Normal returns restore runtime/global metadata and preserve
memory outside temporary RLP scratch. Scalar/bytes/list helpers return their
actual decoded payload pair contained in the original item; fixed bytes proves
the actual bytes tag and exact requested width. The real decoder, nested
access/blob/authorization lists and version-checker producer connections
still need completing; these helper-entry contracts do not assume
those later calls succeed.

The same module now includes complete actual tx_scalar_word and tx_scalar_u256
bounds and normal frames. Their real three-word call to tx_scalar_item gets its
row from actual mapped/stored array cells. The word continuation derives
length<=8 from its own rejection guard, initializes v/j, and ranks its actual
byte-fold loop by length-j; failed byte reads are covered. The wide continuation
derives length<=32 from its own guard and uses current u256_from_be, including
its four-call fast path and slow byte fold. Complete body prices are
60*rowLength+20 (word) and60*rowLength+45 (wide); no incoming eight-/32-byte
cap is required. Actual normal returns retain the RLP outside-scratch frame;
their numeric continuations themselves only read memory and change locals.
Both helpers' real current code signatures/lookups are checked.

The actual decode_blob_hashes copy loop is now checked in TransactionLists.
Its physical model retains the real slice-array cells, per-item byte extents,
allocated aligned output window and actual caller bindings. Each iteration
gets its genuine fixed32 reader entry from those cells, then charges the real
reader and literal memcpy32:60*itemBytes+54 body ticks. A continuing iteration
advances i exactly once, retains the row array and all memory before its buffer,
and restores metadata/scratch cursors. A remaining-work allowance charges
60*itemBytes+55 per remaining row, including the loop tick. Total item bytes
and count are bounded by the actual original input extent, so the complete
copy loop costs<=115*inputLength, including abort/timeout paths. Normal exit
retains its exact final count and physical frame. The actual preceding RLP
conversion and output allocation now supply this model from their own observed
returns. The complete actual decoder costs<=186*inputLength+6, including both
allocations and all stopped outcomes. Its genuine normal return is the actual
(buffer,count) pair, count<=inputLength, with owned aligned32*count output,
observed bounded aligned next heap and the persistent normal frame protecting
all memory before its entering heap and all nonheap globals. No future loop
or allocation success is an entry premise.

The two other nested-list decoders now share a checked actual entry prefix:
rlp_item, real tag guard, current slice conversion, and the real arity guard
(two access fields or six authorization fields). The prefix contributes
<=131*entryBytes+15 plus the field continuation's allowance; that continuation
still needs composition, so this is not a complete helper bound. Its real
Rows retain validated item provenance, stored row words, allocated aligned
array, bounded next heap and the actual persistent frame. Each selected fixed/
wide/word reader gets its real three-/four-word ABI and exact row from those
cells. Normal reader returns retain Rows/input; the checked caller allowances
are60*rowBytes+12(fixed),+46(wide),+21(word). Real bounded-width record stores
preserve the earlier input and separate row array, including tuple stores.
No successful future read, field parse or store is assumed.

The actual authorization six-field suffix is now completely priced and its
normal effects checked. Literal syntax retains all six calls/stores and the
assigned fourth call; checked scalar/four-word shapes derive each actual
flattened write width. Its six distinct rows cost60*payloadBytes+192 rather
than six times the largest field. Normal completion retains the row/input
model, all metadata and memory before the real record and advances the outer
i exactly once. Real item/converter prefixes now also retain saved caller
locals outside it/ent, so the original recs/i bindings supply the record
address. The complete actual authorization iteration costs<=191*entryBytes+207
from its selected outer row and previously allocated record slot. Its actual
normal prefix now exposes the real remaining field run and physical/local
scope restoration. The complete actual iteration retains earlier input,
caller bindings and index+1, with an observed bounded aligned growing heap.
The physical outer loop Model derives each selected row/record entry from
actual input items, stored array cells and the earlier record allocation.
Every real normal iteration retains this model while advancing its index and
heap. A remaining-row charge191*itemBytes+208 gives full loop<=399*inputBytes
for every outcome. Normal loop exit has index=count, preserved original rows/
input/nonheap globals and heap>=its entering heap. The actual initial
conversion and120*count record allocation now supply this Model from their
own observed returns. Complete unchanged decode_authorizations costs
<=470*inputBytes+6 for every outcome. Its normal return is the real allocated
(records,count) pair, count<=inputBytes, owned aligned120*count output and an
observed bounded aligned current heap covering every record, with the shared
persistent frame protecting entering input and nonheap globals. The code
lookup/signature is checked at original index278. No future allocator/field/
loop success is an entry premise.

The access-list storage-key suffix is now checked in AccessKeys, using its
actual slots/keys/j/k bindings (callee formal i remains i). The actual extracted
fixed32 reader/copy loop has the shared per-row charge60*itemBytes+55, full
loop<=115*keyPayloadBytes and normal count/metadata/pre-key-buffer memory
preservation. Actual slots conversion and keys allocation supply its model
from their own returned count, rows and room; no future copy/store success is
assumed. Complete actual afterList suffix, through the key loop, record stores
and outer-index update, costs<=186*keyPayloadBytes+6 on every outcome. Normal
afterKeys completion exposes the real finished key buffer/count, persistent
frame, retained caller bindings and actual remaining record-store run. Its
three real record stores now have exact checked address/key-pointer/count
memory effects, outside-record preservation and actual outer-index advance.
Complete normal key suffix returns an Output carrying owned aligned32*count
keys, actual count<=keyPayloadBytes, observed bounded aligned growing heap
covering the keys, actual stored values and the pre-record/input frame.
The real two-formal tx_list_item caller now derives its contained payload and
actual key-suffix entry. Both distinct field rows cost<=246*entryPayloadBytes+30;
the complete actual access iteration costs<=377*entryBytes+45, all outcomes.
Normal composition of both real field readers is now checked, including the
original sl/addr bindings restored by their own scopes. Complete normal access
iteration exposes its actual stored owned key buffer/count, bounded aligned
heap>=entering heap, real index+1 and input-contained fixed20 address. Parser
scope restoration now explicitly retains original it/ent bindings and payload
lower/end bounds. The physical outer Model now retains all completed records,
their actual address/key/count words, owned aligned key buffers and per-entry
count budgets. Each real iteration preserves earlier records before its current
24-byte output slot and advances the growing bounded heap/index. The complete
outer loop costs<=423*inputBytes on every outcome. Normal exit has index=count,
original rows/input/nonheap frame and all completed records. Summing their
actual stored key counts gives totalKeys<=inputBytes, charged to each original
entry's own byte extent. The complete unchanged decode_access_list body now
costs<=494*inputBytes+6, including actual conversion, output allocation, all
nested work and stopped outcomes. Its normal pair exposes allocated aligned
24*count records, the actual bounded aligned covering heap, original input
provenance, every stored address/key/count and totalKeys<=inputBytes. These
facts survive final scope restoration; the persistent frame protects input
and nonheap globals. No future-success hypothesis is required.

The actual transaction envelope selector is now checked in TransactionEnvelope,
extracted from decode_transaction_rlp279. Typed input skips exactly one byte;
legacy input retains the whole span. Actual assigned rlp_decode_fully calls
and complete selector cost<=60*inputBytes+13, all outcomes. A normal selector
supplies its real complete top item, retained runtime/outside-scratch memory
and original other caller locals. Actual empty guard derives nonempty input;
actual list guard derives list kind, positive header and contained payload
arguments for the real slice conversion. The exact field continuation is
retained on enclosing returns and priced only after this same observed parse.
The complete actual initial setup now costs<=515 source ticks on all outcomes.
Its same observed trace derives nonempty input, the actual first byte<256,
allocation room for400 bytes and the exact cleared record/selector state.
All48 ordinary record words start zero; its last two words hold the actual raw
pointer/length. Initial t0/nfields9/top0 and tx/b0 bindings, bounded aligned
covering heap, real live parser entry, pre-record input/nonheap frame and
normal lexical-return observation are checked. Later work is charged only
at this same initialized state. The real selector now derives type0..4 with
its actual required count:9/11/12/14/13 respectively. It retains the SAME
complete parse, actual top item, other caller locals and input/nonheap frame.
A genuine decoder return reaches its real field suffix with those facts;
normal setup costs16 and its complete reached setup/selector prefix costs
<=60*inputBytes+29. The all-outcome body composition is60*inputBytes+528
plus a field-suffix allowance, required only at that same genuinely reached
parsed type/count state. The actual type store, list guard, slice conversion,
array alias, arity check and k/w initialization now compose to the real field
body in TransactionDecoder. Actual rows retain parsed item provenance, mapped
array cells, count=fieldCount(tag)<=14, live bounded aligned heap, separate
owned400-byte record and payload before that record. Their converter entry
uses the real top-payload arguments, without requiring caller p/len to equal
that payload. All-outcome body composition is131*rawInputBytes+532 plus its
field-body allowance. A genuine enclosing return reaches those
same rows within131*rawInputBytes+33 and retains the exact initialized record
image (selected type, zero fields and original raw pointer/length), original
input/nonheap frame and actual final lexical-return observation. The field
body allowance is now discharged below. Whole-decoder returned-record and
normal frame contracts still need composition.

The complete ORIGINAL current decode_transaction_rlp now has a checked
all-outcome SOURCE call/loop allowance<=2181*rawInputBytes+1023, given its
physical entry (live parser arena, actual bounded aligned heap and input
before that heap). No future field, nested-decoder, signature, allocation or
return premise remains in body_cost. The actual handled decode_transaction
wrapper costs<=2181*rawInputBytes+1024, including real RlpErr translation,
local initialization and return. Their original279/280 declarations are
connected to the same unchanged Software AST. These are source helper
allowances; no global finite target K or whole-main source allowance follows.

Actual fields through data cost480*payloadBytes+250. The access branch
costs554*payloadBytes+19, blob fee/list branch306*payloadBytes+65 and
authorization branch530*payloadBytes+19, including actual reader calls,
allocations, finite record writes, index advances, lexical restoration and
stopped paths. Real type tests select active branches; type3/count14 and
type4/count13 give their actual valid rows. Every normal branch preserves
the same outer input/table/type/count/record facts at the actual next bounded
aligned heap. Final indices are6/8/9/11/10 for types0/1/2/3/4; k+2<count is
checked from those actual advances. The final V/R/S reads/stores/return cost
180*payloadBytes+138. All remaining fields cost1570*payloadBytes+241;
complete fieldBody costs2050*payloadBytes+491, discharging the real row-entry
composition above. No source-program replacement was made.

The complete ORIGINAL279 decoder and handled280 wrapper now also have
normal return contracts for the versioned-hash checker. Returned value is
the SAME allocated400-byte transaction. Its actual stored type is0..4;
record arena/alignment and a bounded aligned covering heap are derived.
For type3, its actual stored256/264 blob pointer/count has owned aligned
32*count bytes, count<=rawInputBytes and actual final heap coverage. Original
input/older words and every nonheap global/runtime field are retained by a
PersistentNormalFrame at the original incoming heap/record frontier.

fields_normal composes real chain-ID, vector declaration, nonce, fees,
gas, destination, value, data scope, access/blob/auth branches and V/R/S.
Each actual continuing state retains the correct field index and earlier
type word, including scoped v/data restoration. body_normal composes that
same execution with setup/parser/arity and initializedMemory snapshot;
the type is the actual selected tag, not a supplied output hypothesis.
Wrapper body_normal includes real tx/rc declarations, same decoded callee
result and final return/scope restoration. Its RlpErr handler raises TxErr
and cannot fall through; a normal wrapper call therefore supplies a real
checked callee return. All failed outcomes retain the complete source costs
above. Further VM-specific returned fields can be exposed when their actual
callers need them. No source-program replacement was made.

## Cache restriction removed

The actual hash's mandatory block reads give a fixed spatial allowance.
A returning absorb block must read its first actual word or unaligned byte
inside ordinaryDomain, whose exact exclusive upper end is33806089704.
Every continuing hash block advances136 without wrap and decreases a finite
rank; the last failing read and all timeout/abort outcomes are charged too.
Complete hash body<=10937265093 source ticks, caller<=10937265094, for any real
64-bit count. Actual normal return derives count<33806089976 and the genuine
remainder<136, supplying the existing padding/memory frame's needed condition.
call_domain_span_frame needs only the count's real64-bit representation.

`H(C)=CurrentKeccak.Hash.boundedBodyPrice(C)` equals
`44*(min C 33806089976/136)+689`: small inputs retain the old linear price;
large counts are clipped at the spatial price. node_hash_cached and
node_write_ref have actual clipped body/caller prices and real normal frames.
The complete branch/extension/finish/fill/root clients now use these clipped
prices. **cacheSmall has been removed from all those contracts and records.**
CachedLengths remains a convenient parameter for tighter instantiations, but
CachedLengths graph (2^64-1) follows unconditionally from the stored word type.
Persistent.word_limit retains every real physical fact at that universal cap.
Thus initial cache allocation/history is no longer an entry blocker.

Checked source helper formulas, with C=cacheLimit and V=valueLimit:

- Branch finish:16*(H(C)+48)+CopyAny.price(V)+114.
- Leaf finish:CopyAny.price(compactLength)+CopyAny.price(valueLength)+75.
- Extension finish:CopyAny.price(compactLength)+H(C)+103.
- Fill body:3+(251658240/2+27)+(stepPrice(C,V)+1)*521215+1.
- stepPrice=32+max(251658240/2+29,finishPrice), where finishPrice is the maximum
  actual finish caller allowance, compact copies capped by251658240.
- Root body:Fill.bodyPrice(C,V)+H(C)+48. Each actual helper caller adds1.

At C=251658240,V=268435456, checked arithmetic still gives fill body
858256814537851 and root body858256895957420. At the unconditional word cap
C=2^64-1 and the same V, checked fill body is91389929611497531 and root body
91389940548762672, caller91389940548762673. These are physical-entry **source
helper** allowances, not a global target K. Review this spatial slack after
whole-program closure, especially charging genuine first hashes to advancing
persistent allocations instead of charging every child the worst case.

The complete actual versioned-hash checker792 is now checked in
VersionedHashScan, including nonempty arrays. Each SSZ row supplies its real
pointer/length expressions and decoder physical entry from actual stored cells,
input containment and bounded aligned current heap. Normal continuation protects
the row array and carries the growing heap and actual i+1 to the next row.
Actual tx_is_blob789 opens blob fields only for its genuine true result;
complete memeq32 caller<=5 and signed inner hash loop<=6 per remaining hash.
Complete transaction iteration<=2187*rawBytes+1026; outer overhead adds1.
Real adjacent SSZ offsets telescope: raw bytes+4*count<=sliceBytes. Thus the
full outer loop and complete checker body<=2187*sliceBytes on every outcome,
without multiplying the whole input by transaction count. Actual Data geometry
derives the uniform body allowance550369607472; scoped caller<=550369607473.
The complete returned frame covers BOTH genuine early mismatch returns and
normal loop exits through the final tail/declaration restores. It protects
all memory before the actual entering heap, every nonheap global/runtime field
and an actual bounded aligned growing final heap. The actual reached scoped
caller therefore retains real decoded Data via Data.of_persistent_normal.
No zero-count, per-transaction heap release, readonly decoder or future-success
premise is used. TransactionData now uses these contracts and has been revalidated through
the actual block-execution caller. Its obsolete zero-only VersionedHashes
namespace and false whole-decode readonly prefix frame have been removed.

The complete actual run_attempt prefix now reaches its real execute_block
caller within182603460060252670 source ticks, retaining the genuine decoded
Data, physical header, actual block environment and initialized state records.
Header hashing and comparison, nonempty version check, header validation and
block environment setup are all connected to the complete current header
prefix. HeaderHash's tight encoder output<=916 remains valid from its actual
FieldFacts; the separate payload-header encodedBound8388608 does not invalidate
it. The same-execution record trace retains the actual pre-workspace
StablePrefix and current StateFrame. The complete actual execute_block initialization is now checked for the
actual decoded count, including nonempty arrays: both opening reads, owned
output, both16*count+16 arrays, fresh log/request/return lists, actual output
transaction count and initialized BAL tables. It stops or reaches its actual
first mandatory system call within161 source ticks while retaining the real
input/header/environment and earlier state records. Later execution is open.

The actual first system-call argument bridge and fresh-state prefix are
now checked in FreshTransactionMemory. Installed code plus the SAME argument
read/lookup derives the actual target word, input pointer+26 and length32;
no typed address global or future normal callee outcome is required. Actual
state_fresh_tx body<=74/caller<=75 and its real eight-table transaction state
are revalidated. The first parent caller either stops within76 source ticks
or reaches its literal ext_code_of continuation with the same target/data,
owned fresh state, bounded heap and retained earlier MPT record ownership/
contents. AccountAccess's first insertion/empty transaction-cache miss prefix
<=31 is also revalidated. Complete ext_code_of/account/pre-state and system
transaction execution remain open; these prefixes are not full helper bounds.

## Remaining plan

1. Continue actual system-transaction execution from the checked nonempty
   execute_block initialization. FreshTransactionMemory and the genuine first
   call/fresh-state input/record bridge are now checked. Expose the cache/trie
   facts needed by account/pre-state access from actual prior initialization
   and setters, then complete ext_code_of/account helpers and the mandatory
   system-call path. No empty-count opening/array shortcut remains
   in the now checked block initialization.
2. Finish current table/pre-state/system-call/VM/finalization execution and
   complete main, preserving covered rejection/trap and accepting-output cases.
   Reuse old proofs only after revalidation against mapped scratch behavior.
3. Complete uniform source-to-target transport, include straight-line work,
   evaluate explicit K and review dominant slack. Do not optimize the guest.
4. Remove unused alternate Pancake implementation code, obsolete flat-only or
   empty-input shortcuts and dead dependencies. Recheck the final theorem,
   permitted axioms, fixed-file integrity and submission isolation. Arrange
   final verification on an allowed host; report its actual scope.

## Checkpoint and reproducibility

Latest selected check: `first-system-entry-v3.log`, PASS3332jobs,
exact root FreshTransactionMemory: actual first system-call ABI/input bridge,
fresh transaction state/retained MPT record frame and existing account-access
prefix. All printed axioms permitted. Nonempty block initialization:
`block-execution-count-v2.log`, PASS3329. Actual main prefix to executor:
`transaction-data-versioned-v2.log`, PASS3326. Incremental policy
PASS65536entries/2490459531bytes; full fixed policy revalidationfalse.
Inventory8745Solver modules, replacement AST reverse closure0, frozen6957
files unchanged. Registry2170modules/8291printed facts at6957;
historical8705/20518 is not whole-current validation. Package entry limit
reached: reuse modules or remove checked obsolete dependencies before adding
another. Usage last observed71%, one reset credit, ordinary allowed at
1793486891. Claim infinity; no full verifier/global finite target K.


## Actual first scalar leaf retained — 2026-10-31

The same actual original first htab_new_leaf execution now establishes all
11 final header words, its initialized node1 fields, order[0]=1, count1,
next-node2 and leaf marker key*8. The unchanged htab_set root store is proved
to install root1 while retaining those facts. This ScalarSingle result is
carried through every real declaration/call scope, first_set_normal, the
actual empty account-cache getter, and AccountAccess.to_pre_state. No key-byte
identity or future successful read is assumed. Earlier state, other empty
transaction tables and the existing source prices remain retained.
Selected FreshTransactionMemory build scalar-single-caller-v2.log PASS3332,
28.48s, peak2691744KiB; 2170modules/8297facts checked against6957805e.
Incremental policy PASS65536entries/2490476449bytes; fixed-file revalidation
false; no new module. No global finite target K/full verifier; claim infinity.
Next: use the derived actual singleton leaf to bound the repeated access-table
setter in get_pre_state_account_optional; derive the real BS pre-state cache
image from state_init rather than assume it at the future lookup.


## Actual singleton traversal and caller — 2026-10-31

The derived actual first insertion now feeds the real htab_find_leaf body.
Scalar leaf step breaks on key*8 without evaluating the query-bit branch;
actual traversal takes exactly one funded loop tick (zero clock times out).
Whole body costs<=1 on every outcome, returns leaf1 on a normal return and
retains every nonlocal field. Original scoped caller costs<=2 and resumes its
same continuation with actual leaf1 and the full memory frame. This is not
a new global table-image assumption: ScalarSingle is established by the
actual first insertion and already retained to AccountAccess.afterMiss.
Selected FreshTransactionMemory root scalar-single-trace-v1.log PASS3332,
32.17s/peak2694012KiB. Registry2170modules/8301facts at6957805e; incremental
policy PASS65536entries/2490486046bytes; no new module, fixed revalidationfalse.
Latest usage1793487560:72%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite targetK/full verifier; infinity.
Next repeated-set proof: feed scoped_scalar_single_trace into unchanged
Set.afterStride; scalar field reads provide keylen20,stride24,keys pointer;
actual memeq20 must handle every observed result/failure. If its equality
branch cannot be derived from a justified source-key preservation fact,
price the actual first-difference/second-search/new-leaf path too. The existing
general Set proofs assume32byte keys/marker256 and cannot be reused with20
silently. A possible targeted alternative is retaining the actual fork_init
beacon allocation and immutable20byte source through main; current Data does
not yet establish this. BS pre-state cache initialization ownership still
must be derived separately, as previously recorded.


## Scalar leaf constructor at any available node — 2026-10-31

Generalized real copy-argument evaluation and post-node constructor cost to
arbitrary actual node indices. Original first-leaf theorem now instantiates
the shared no-grow constructor proof, removing its duplicate traversal.
ScalarFields.after_index derives preservation of actual keylen/stride/key
base through the real node increment. Whole scalar_no_grow_cost includes
node allocation, variable-width memcpy and every real store/failure/timeout:
body<=CopyAny.price(key.toNat)+2. The actual derived singleton metadata gives
index2, empty free list and existing capacity, so scalar_single_cost prices
the real second leaf without assuming a fresh table or successful key reads.
Selected FreshTransactionMemory scalar-second-leaf-v1.log PASS3332,
31.85s/2688664KiB. Registry2170modules/8306facts at6957805e; incremental policy
PASS65536entries/2490491703bytes, fixed revalidationfalse; no new module.
No global finite targetK/full verifier; claim infinity.
Next derive scalar FirstDiff bounded returned position without a32byte view,
then single-node second search and second leaf's retained no-grow metadata.


## Actual scalar first-difference and second search — 2026-10-31

FirstDiff scalar_body_returns derives a bounded returned position solely
from the actual outer unsigned byte counter and inner signed0..7 bit
counter. At any length<=60, a real normal return is a word at position
<=8*length. No ByteView, guessed key equality, successful future read or
completed auxiliary scan is assumed. scoped_scalar_trace retains the same
actual returned position, full physical frame and original continuation;
all stopped outcomes cost<=9*length+1 (181 at20bytes).
Set.scalar_seek_step/loop prove the actual one-node insertion search breaks
immediately at its scalar leaf when d<=marker, with exactly one funded tick
or a clock-zero timeout. The difference result above supplies the numerical
condition; the actual singleton still needs connecting through the setter's
memeq/difference/setup continuation and its derived physical node mapping.
Selected FreshTransactionMemory scalar-second-seek-v2.log PASS3332,
239.07s/peak2830588KiB. Registry2170modules/8313facts at6957805e; incremental
policy PASS65536entries/2490510785bytes; fixed revalidationfalse; no newmodule.
Usage1793488128:72%, ordinary allowed; one reset credit retained.
No global targetK/whole-main allowance/full verifier; claim infinity.


## Complete real repeated account-access setter — 2026-10-31

The whole unchanged scalar singleton htab_set body now costs
CopyAny.price(key.toNat)+13*key.toNat+10; its actual ordinary ignored caller
adds1. For the real20byte access table, these are294body/295caller ticks.
All genuine FindLeaf, memeq, first-difference, one-node second-search,
second-leaf/internal-node constructors and post-constructor splice branches
are included. Reads, comparisons, copies and stores may fail; no equal-key
result, ByteView, predicted returned leaf or later successful scan is assumed.
The same actual bounded first-difference return feeds the real second search.

Normal scalar leaf construction now retains its exact generic index/count
header and complete external memory frame. On the derived singleton, it
returns node2 and proves the following allocator has actual index3, unchanged
free list/capacity and real node-array pointer. Original first-leaf normal
results now use this same generic execution; removed obsolete fixed-index
copy-state/geometry derivations rather than retain duplicate proof chains.
PreStateAccount checks original get_pre_state_account_optional338 and its
actual repeated htab_set prefix. Its ABI carries the singleton/remaining TS
context already produced by AccountAccess.to_pre_state; first_set_cost
prices that exact runtime access call at295, with real TS field loading.

Selected FreshTransactionMemory scalar-repeated-account-v1.log PASS3332,
39.57s/peak2701296KiB. Registry2170modules/8343facts at6957805e; incremental
policy PASS65536entries/2490560741bytes; fixed revalidationfalse; no newmodule.
Usage1793489080:72%, ordinary allowed; one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next prove the repeated setter's NORMAL outside-table frame (its cost is
complete), carry the remaining TS/old MPT ownership through that real call,
then derive the real BS+16 cache initialization/image needed by its getter.


## Complete repeated setter memory frame and pre-state prefix — 2026-10-31

Both normal branches of the unchanged scalar singleton setter now return
literal0, retain every nonlocal runtime field and preserve every memory word
outside the same complete table allocation. The real second leaf/internal
constructors, actual bounded-difference seek, all three parent stores, either
actual key-bit child-link branch, root attachment, comparison/update path and
all lexical/caller restorations are included. The ignored caller restores
its actual saved locals. The previous294body/295caller tick bound is retained.

AccountAccess now retains an AccessState produced by the actual first
insertion: its pointer field, singleton, allocation after the transaction
record, and full table separation. The real read-only cache getter carries
all these to the pre-state call. PreStateAccount.first_set_normal uses the
new repeated-call frame to retain all OTHER fresh TS tables, full record
pointers, separation and earlier persistent state, without claiming the
modified access table is still a singleton. to_after_set reaches that actual
pre-state body's original BS-cache getter within295ticks or stops without
an enclosing return. No cache contents are yet assumed at that getter.

Selected FreshTransactionMemory scalar-repeated-account-frame-v1.log PASS3332,
12.62s/peak2746944KiB. Registry2170modules/8369facts at6957805e. Incremental
policy PASS65536entries/2490622675bytes; fixed revalidationfalse; no newmodule.
Usage1793490355:72%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next derive actual block-state table images from state_init, preserve them
through main and first system/account access, then bound the actual BS+16
cache getter, record_pre_state_read and workspace account/trie calls.

Detailed chronological proof history: `work/agent-notes/PROGRESS.md`.
Reproducible evidence: `proof-checks.json`, `policy-check.json` and
`original-plan-inventory.json` in that directory. Failed builds are not indexed.

Decoder/envelope work now resides in TransactionDecoder, importing the
completed TransactionLists helpers. Build the exact TransactionDecoder root
for later decoder edits. VersionedHashScan imports it and houses the actual
version-check loop/caller proofs; use that exact root for checker edits. These
splits change proof organization only.

Use exact selected Lean roots only, artifact cache disabled, two workers and
the8GiB resource guard. Freeze candidate edits during builds/policy checks.
Do not run the full verifier, Solution root or an unqualified full build here.
After a successful selected build, record its log basename, regenerate inventory,
run incremental policy and git diff --check. Commit concrete checked work and
immediately push each commit to georg with the existing private push helper;
verify clean local/remote agreement. Never print that helper, .bashrc or tokens.
Check account usage periodically; account resets, not context resets, were
requested. One reset credit is available; preserve it until needed.


## Actual initialized block-table images — 2026-11-01

The complete unchanged state_init now derives empty scalar headers for all
seven actual BS tables and pairwise separation of their complete allocations.
Their real BS pointer stores, key widths/capacities, positions after BS+80 and
ends below the actual heap are retained through subsequent table allocations,
scratch setup, the16MiB journal allocation and normal caller restoration.
Only already constructed tables enter the partial invariant. No future table
contents, successful writes or getter context are assumed.
The stronger Complete result is connected through the real workspace/root
suffix, whole state_init and StateInitReturned.complete_records. Existing
physical-only APIs project from it. Next carry the actual completed snapshot
through the header/main prefix and derive the first BS+16 cache getter entry.

Selected FreshTransactionMemory state-init-complete-fresh-v1.log PASS3332,
140.49s/peak2846452KiB; StateReturnedData state-init-complete-tables-v1.log also
PASS2906. Registry2170modules/8393facts at6957805e; incremental policy
PASS65536entries/2490659343bytes; fixed revalidationfalse; no newmodule.
Usage1793491867:73%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.


## Real block-table images through main and first cache miss — 2026-11-01

The completed state_init snapshot now follows the same actual main prefix
through transaction scanning, complete payload header, header validation and
block-environment setup to beforeExecuteBlock. Older physical-only APIs are
projections of the stronger traces. InitializedRecords retains the original
completed snapshot, its actual entering header heap, the derived workspace
lower bound and the existing earlier-memory frame. Its tables theorem derives
all seven current empty images/separation inside that interval. The lower
bound2701135464 follows from the real decoded input, record extent and heap;
no stronger unexplained memory interval or future getter contents are assumed.

FreshTransaction.Context.initialized_records transports this same snapshot
through the genuine fresh-state/access-setter frames. The original pre-state
BS+16 getter now derives its real20byte/cap256 table and arguments from those
facts. Its complete scoped read either stops within2source ticks or returns
the actual absent pair and reaches the unchanged miss suffix with memory,
transaction tables and initialized records preserved. to_after_cache connects
the preceding repeated access insertion: whole actual prefix<=297source ticks,
including stopped outcomes, rather than assuming a successful read.

Selected FreshTransactionMemory block-tables-pre-state-prefix-v1.log
PASS3332,13.00s/peak2685212KiB; earlier block-tables-cache-miss-v1.log
PASS3332,80.43s/peak2851980KiB. Registry2170modules/8408facts at6957805e;
incremental policy PASS65536entries/2490681122bytes, fixed revalidationfalse;
no new module. Usage1793492250:73%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next follow original record_pre_state_read (BS+72) and ws_get_account_optional.


## Actual pre-state read recording and workspace entry — 2026-11-01

The complete current record_pre_state_read body now costs29source ticks;
its genuine ignored caller costs30. Its real BS+72 cell supplies the
20byte/cap256 empty table and setter arguments. Normal execution derives
literal0, the actual singleton, full scalar-table write footprint and
restored caller locals. No successful key copy or future table is assumed.

Recorded models the changed BS+72 table separately from the other six BS
empty images and all real pointer/allocation separation. Its earlier-memory
frame ends at BS+80, protecting WS/MPT contents without asserting the modified
BS table remains unchanged. The later transaction tables retain their actual
images; their earlier-memory snapshot is rebased to the new current state.
PreStateAccount.to_after_record connects repeated access insertion, cache
miss and read recording to the unchanged ws_get_account_optional caller:
whole actual prefix<=327source ticks, with stopped outcomes retained.

Selected FreshTransactionMemory block-read-record-caller-v2.log PASS3332,
15.25s/peak2692276KiB. Registry2170modules/8420facts at6957805e; incremental
policy PASS65536entries/2490705380bytes; fixed revalidationfalse; no newmodule.
Usage1793492548:73%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next derive the workspace/trie graph and values from actual state_init,
retain them through the proved main/recording frames, and complete the real
workspace account lookup. Existing rich witness proofs require revalidation
against the current NodeLookup.Database/materializer invariants.


## Current trie registry decode and resolve revalidated — 2026-11-01

RichInvariant now extends the actual current NodeBuild.Data-indexed physical
materializer invariant. NodeRegistry.after_live_frame and ChildViews.live_frame
use the current decoder's true earlier-memory frame, protecting completed
nodes/values and pending branch children under the high scratch layout.
Terminal leaf/hash registration retains real value bounds and closed children;
current resolver results include their actual allocation and heap caps.
RichInvariant.decode_normal and resolve_normal now preserve that registry,
branch exclusions, child membership and strictly decreasing physical rank
through every actual normal decode/resolve iteration. No old RootBoundary,
low scratch assumption or future graph is supplied at those transitions.
The return-mode registry and whole materializer/initializer graph connection
still need completing; the whole account lookup is not yet bounded.

Exact selected roots WitnessCoreRichResolve, WitnessCoreRichDecode and
FreshTransactionMemory: current-rich-resolve-v1.log PASS3351jobs,
5.22s/peak1992464KiB. Registry2182modules/8454facts at6957805e; incremental
policy PASS65536entries/2490707063bytes; fixed revalidationfalse; no newmodule.
Usage1793493256:73%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.


## Complete current materializer graph and state_init root call — 2026-11-01

The complete current return path now retains the materialized trie graph,
bounded values, child closure, branch exclusions and actual allocation
regions through child/OCC/index stores, real final-value parsing, branch
completion/pop, extension construction, cache stores and scope restoration.
The proofs use the current high scratch layout and the actual parser's
outside-scratch frame. Obsolete low-scratch/RootBoundary premises have been
removed from the revalidated rich loop and normal body contracts.

Both actual caught materializer wrappers and their real scratch release
retain the same graph and exact returned member. The whole current root
decoder handles its genuine empty/lookup/materialize/cache branches and
returns RichOutput with that graph. Its root-cache allocation/copy proof
exposes exact heap advancement and earlier-memory agreement except for the
registered root's cache word; graph/value fields are proved disjoint from
that word. StateInit.root_call_normal_rich now connects this stronger result
to the real initializer caller. The existing physical-only API projects it.
Preserving this graph through the remainder of state_init/main and completing
the workspace-account lookup remain; no final global bound is claimed.

Selected FreshTransactionMemory current-rich-state-root-v1.log PASS3374,
156.71s/peak2859592KiB. Whole rich root current-rich-root-complete-v3.log
PASS1828; final cache formatting check current-root-cache-format-v1.log
PASS1745. Registry2205modules/8504facts at6957805e; incremental policy
PASS65536entries/2490723876bytes; fixed revalidationfalse; no new module.
Usage1793493852:74%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.


## Initialized trie retained through main and read recording — 2026-11-01

The actual block-state suffix now protects every word before BS, while its
physical workspace frontier stays independent. Exact normal workspace stores
and the genuine BS allocation identify the only earlier-memory changes:
WS24 and WS32. The decoded root graph lies after WS+40 and before the actual
entering heap; both workspace stores, the next table allocation and the whole
BS/scratch/journal suffix therefore retain it. Old initializer suffix APIs
project from the stronger proofs; duplicate proof chains were removed.

WorldState now carries the initialized BS tables, actual WS24 root pointer,
closed node registry and bounded values with all nodes before BS. Complete
state_init derives it from root_call_normal_rich. The same actual main prefix
retains it through transaction scanning, payload header, validation and block
environment setup. InitializedRecords retains this genuine origin snapshot.
The real read-recording mutation keeps it together with the narrower frame
below BS+80; Recorded.world derives a usable CURRENT trie and WS24 pointer
after that mutation. No future graph is supplied as a helper-entry premise.

Selected FreshTransactionMemory state-init-world-recorded-v1.log PASS3374,
157.83s/peak2872924KiB. Registry2205modules/8515facts at6957805e; incremental
policy PASS65536entries/2490741572bytes; fixed revalidationfalse; no newmodule.
Usage1793495116:74%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next connect the current workspace-account lookup, deriving its nibble/hash
workspace globals and physical protection from the real startup/main trace.


## Actual nibble workspace through main and trie protection — 2026-11-01

The real startup allocation sequence now derives mpt_nib_scratch=
2701134704. Its fixed64byte extent ends at2701134768, before the actual
copied input and initialized workspace. Existing initializer APIs project
from first_four_complete. The same global follows the actual remaining
startup, decoder/root allocation, complete request hashing, verification
wrappers, state initialization, payload header, validation and block setup.
CurrentHash.WorkspaceEntry and CurrentVerify.Data carry the derived cell;
all their actual frame/heap/global transports now retain it. No unexplained
nibble-pointer premise is added at the main input producer.

Recorded.lookup_world strengthens the actual retained read-recording trie:
all its structural and value fields are protected from the fixed nibble
buffer, using their real regions after WS+40. Recorded.root_cell derives
the typed current WS global and mapped WS24 word from that same actual
record. No future trie graph, contents or successful hash call is assumed.
The actual workspace-account hash/lookup and whole account result still
need connecting; their complete current source allowance is not claimed.

Selected FreshTransactionMemory actual-nibble-main-v2.log PASS3374,
50.30s/peak2811652KiB; startup actual-nibble-startup-v1.log PASS1677,
202.20s/peak2104156KiB. Registry2205modules/8521facts at6957805e;
incremental policy PASS65536entries/2490751372bytes; fixed revalidationfalse;
no newmodule. Usage1793496518:75%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next use the current software Keccak cost and observed normal-call frame
(no cryptographic oracle premise or initial address ByteView), retain the
real initialized trie across its temporary hash output, and complete the
original ws_account_leaf/ws_get_account_optional prefix. Thread only actual
startup workspace globals through fresh-state/access/read-recording frames;
respect stopped outcomes and derive allocation room from real guards.


## Current trie lookup and actual account workspace entry — 2026-11-01

The complete unchanged current trie_lookup now has its checked Software
index241, full2090tick body/2091tick caller allowance and actual scoped
normal binary/payload result with bounded values and output-only frame.
The ranked trie_walk, leaf/extension/branch progress and normal values are
revalidated. Missing direct imports were restored; core strongRecOn now
supplies the exception-loop inductions. Comparison20/52byte kinds and word
mapping no longer import obsolete hash-table hashing/find_slot programs.
The actual current memeq ABI is reused, and its walk exception proof is
local to that comparison. Source/guest bytes are unchanged.

AccountLookup.Environment extracts the real software Keccak environment,
endianness and nibble cell from Data. FreshTransaction.Context transports
it from the actual fresh-state origin through retained runtime/global
frames, allowing only its real heap/TS/journal updates. The real read-record
caller now exposes its metadata frame; the old miss_record_trace projects
from miss_record_trace_complete. to_after_record_environment combines that
frame with the existing actual prefix, preserving all stopped outcomes and
the327tick price while deriving workspace facts at the reached original
ws_get_account_optional caller.

AccountLookup.Entry.of_recorded packages that same reached environment,
WS global/mapped record, initialized current trie between WS+40 and BS, and
actual heap beyond BS+80. No temporary32byte allocation room, initial address
ByteView, successful hash or future account result is supplied. of_frame
transports the real registry across helper entry/local binding. Complete
ws_account_leaf/ws_get_account_optional source costs remain to connect.

Selected FreshTransactionMemory current-lookup-entry-v2.log PASS3431,
16.65s/peak2733012KiB; exact TrieLookupCall/TrieLookupCallValues roots
current-trie-lookup-v5.log PASS827,43.88s/peak1716220KiB. Registry2263modules/
8682facts at6957805e; incremental policy PASS65536entries/2490763449bytes,
fixed revalidationfalse; no newmodule. Usage1793497121:75%, ordinary allowed,
one reset credit remains. No whole-main allowance/global finite target K/
full verifier; infinity.
Next price actual Software ws_account_leaf(index331): real mark, classified
32byte allocation, current software Keccak<=690caller ticks even for failed
address reads, retained initialized graph through the normal hash frame,
then scoped trie_lookup and heap release. Derive room from allocation's own
guards. Actual entry fields place structural/value words before BS and after
WS+40; fixed state/pad buffers are below them, while temporary output follows
BS+80. Use current Keccak call_span_frame; do not revive the legacy
cryptographic-oracle EntryData API in WsAccountLeafProgram/Cost. Then retain
actual lookup values for ws_get_account_optional's real decoding branch.


## Complete current software account-leaf allowance and result — 2026-11-01

AccountLookup.Leaf now uses actual Software ws_account_leaf(index331).
The whole body costs<=2784source ticks and its real caller<=2785 on every
outcome. This includes heap_mark, the genuine32byte allocation, actual
software Keccak<=690caller ticks, initialized-trie lookup and release.
CurrentAlloc.scoped_classified retains failed allocations and derives room
from normal guards; allocated_entry shares that actual continuation between
cost and normal-result proofs. No initial temporary-room premise remains.
Bad address reads may stop in the actual software hash; no initial address
ByteView or cryptographic-oracle EntryData is required.

The same observed normal hash retains WS24, every structural/value field,
closed initialized trie, real workspace globals and bounded current heap.
The graph lies above the low fixed state/pad/nibble buffers and before BS;
temporary hash output lies after BS. Actual scoped lookup then returns the
binary/payload triple with a mapped payload bounded by1024 and its real
witness-value property. That result is connected through release, allocation
scope restoration and the full saved-mark scope. All normal child execution
and allocation room come from that same full observed run.

Leaf.scoped_classified preserves stopped outcomes or exposes the original
continuation with its actual answer within2785ticks. Optional.body_shape/
original_code check the real ws_get_account_optional(index332), and
Optional.leaf_trace connects that complete leaf caller to its unchanged
absence/account-allocation/decoding suffix. The full optional provider,
pre-state getter, system transaction and whole main are not yet bounded.

Selected FreshTransactionMemory current-account-provider-prefix-v1.log
PASS3431,19.77s/peak2749028KiB. Registry2263modules/8703facts at6957805e;
incremental policy PASS65536entries/2490800359bytes; fixed revalidationfalse;
no newmodule. Usage1793497725:75%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next derive the leaf's actual restored heap and nonheap-global/earlier-memory
frame for the provider continuation; do not assume that post-lookup heap.
The current normal result already supplies bounded mapped payload, but full
RLP account decoding may additionally need its actual earlier-input interval
and scratch workspace. Retain those from the real state/lookup frames,
revalidate current decoder helpers, and complete the original provider's
absence/56byte allocation/decode/return branches. The old WsAccountLeafHeap/
Cursors/LookupGlobals modules still import legacy oracle/hash code and old
heap ceilings: reuse their proof structure only, with current software
Keccak globals and actual current allocator caps. Do not import that chain.


## Real restored account heap, scratch and payload bounds — 2026-11-01

The complete current leaf now preserves every nonheap global on all
outcomes. Its actual normal release/return restores the saved heap exactly,
without assuming a later release or ordering that saved mark below the
current heap. This is connected through actual hashing, nibble lookup,
allocation scope and original heap_mark. Leaf.scoped_complete supplies the
real restored heap beyond BS+80 and retained workspace at the genuine
provider continuation, with the same2785tick allowance and stopped outcomes.
AccountLookup.Environment now also carries the actual startup ArenaState;
Data, fresh-state/access/read-recording and all leaf transports derive and
preserve its true2965299200scratch/2952790016frame cursors.

WorldState.world now retains db<=WS. The real initializer derives it from
its actual completed node-database geometry and table-end-before-heap fact,
then after_root_world preserves it with the same concrete registry. It
survives scope restoration, main, initialized records, read recording and
leaf hashing/lookup. No database-order hypothesis was added at the main
producer. The leaf's actual normal value now exposes this retained db bound
alongside its mapped <=1024byte witness-value result.

Optional.leaf_trace_ready reaches the original absence/decode continuation
with actual startup scratch, restored bounded heap and a genuine leaf local.
Its nonempty payload lies after2701131776 and ends before WS, hence before
the current heap. Zero length remains explicit; no pointer-order fact is
invented for that case. The original absent triple returns sentinel1 with
zero further source ticks. The present triple reaches the unchanged56byte
allocation/decode/return suffix. These actual Software suffix shapes and
both guards are checked; complete provider/decoder costs remain open.

Selected FreshTransactionMemory current-account-provider-ready-v2.log
PASS3431,25.28s/peak2754608KiB; current-account-value-bounds-v1.log PASS3431,
178.68s/peak2895552KiB. Registry2263modules/8720facts at6957805e; incremental
policy PASS65536entries/2490826381bytes, fixed revalidationfalse; no newmodule.
Usage1793498508:75%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next revalidate/port current decode_account_from_leaf(index267). The existing
AccountDecodeCost chain still has old index269 and a low-scratch/Above frame
assumption cursor<=cutoff<=input. Actual input precedes the current high
scratch interval, so derive the correct Outside/below-frame behavior from
the real live-arena proofs; do not apply that old hypothesis. Ready.live_arena
supplies Rlp.LiveArena, not Rlp.Validation.LiveArena. Nonempty Ready.leaf
payload ends before restored heap, and the actual following56byte allocator
can derive its own room/output. A zero-length hit must be priced via the
decoder's actual length guard, without requiring its pointer<=heap. Preserve
both absence and all stopped/malformed decode outcomes. Earlier-memory/trie/
BS/TS frames across the complete leaf/provider still need their full caller
connections for subsequent cache writes.
