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


## Complete current account decoder, provider and first pre-state costs — 2026-11-01

The real Software decode_account_from_leaf now checks at index267. Its
Current.body_cost covers every outcome within191*length+261source ticks;
the actual caller adds one. Current field views own the real input and
persistent slice array below2952790016. Every real field parser supplies
its Outside high-scratch frame, preserving those bytes and record words.
Current list conversion derives its actual array/count, allocation room and
bounded heap. Four-field count/type/length guards, nonce/balance loops and
output suffix are included. The caught full decoder uses its actual current
normal result/frame; the original MPT handler cannot continue after RlpErr.
No old cursor<=cutoff<=input premise is used by these Current proofs.

Only nonempty payloads need end<=heap. Zero length has unrestricted pointer
order and fits from its64bit representation; an actual Complete return
would force positive length, so the same decoder guard discharges that case.
The legacy slice/account contracts encountered by these selected roots now
use the current2952790016heap cap instead of the old33806089496memory end.
Their broader physical-memory conclusions remain weaker projections.

The real ws_get_account_optional now includes absence return, classified
56byte allocation, actual current decoder and literal final return:
body<=198632, caller<=198633source ticks. No future allocation room is
supplied. Optional.Ready carries the original WS lower bound as well as
actual restored heap/scratch and bounded leaf result. The decoder output
mapping follows from that same allocation and its actual guard.

The actual first pre-state getter connects its previously proved327tick
repeated-access/cache-miss/read-record prefix to this complete provider:
PreStateAccount.body_cost<=198960 and real caller<=198961. These apply to
the proved fresh/access-singleton/initialized-record context, not arbitrary
later cache states. All early stops, malformed reads/RLP, exceptions and
normal outcomes remain in the allowance. No whole-system or main bound is
claimed. Normal account images and memory frames still need caller links.

Selected FreshTransactionMemory current-pre-state-account-cost-v1.log
PASS3459,27.39s/peak2810232KiB; AccountDecodeCost current-account-decode-v2.log
PASS1426,21.98s/peak1948908KiB. Registry2291modules/8807facts at6957805e;
incremental policy PASS65536entries/2490872288bytes; fixed revalidationfalse;
no newmodule. Usage1793499422:76%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next derive the genuine provider/pre-state normal account result and earlier
memory/BS/TS frames, then bound the first get_account_optional return
and its enclosing first mandatory system/ext_code path. (Correction: the
actual getter reads the cache but performs no account-cache fill.) Current decoder
costs are under Mpt.AccountDecode.Current in the existing Account* files;
use Current fields/Outside APIs rather than their old low-scratch views.
Scratch and persistent allocation writes must preserve the real input and
initialized table images needed after the call; low hash/nibble scratch
writes are real and must be excluded from claimed unchanged intervals.
Several unvisited legacy normal/image consumers may still need their heap
caps and low-scratch interfaces ported before reuse. Current source, fixed
semantics/ROM/dependencies remain unchanged.


## Complete first optional/required account lookup costs — 2026-11-01

The actual first get_account_optional now includes the proved31tick
access/cache-miss prefix, the whole198960tick pre-state getter and its
literal return: AccountAccess.body_cost<=198992, caller<=198993.
The current acct_new/acct_empty/acct_copy catalogue now selects actual
Software functions at327/328/329 and imports the small original-entry
view, avoiding the stale unrelated GasBudget catalogue. The real empty
constructor costs3bodyticks,4caller ticks on every outcome. Combining
this actual missing-account branch gives AccountRequired.body_cost
<=198997, caller<=198998 for the first get_account.

These are source-clock costs under the real fresh/access/initialized-record
context, including stopped outcomes. The unchanged actual optional getter
returns its pre-state result directly; it never writes the account cache.
The earlier planned cache-fill step was an incorrect source reading and is
removed. The next real ext_code_of stage needs normal account data and
protected initialized tables across this getter, then get_code. That helper
checks the empty hash, TS+48 and BS+48 code caches and records the read at
TS+40 before querying the genuine WS+16 code database. Its complete bound
and memory contracts are still open.

Selected FreshTransactionMemory current-required-account-cost-v2.log
PASS3461,32.96s/peak2817284KiB. Registry2293modules/8824facts at6957805e;
incremental policy PASS65536entries/2490883414bytes; fixed revalidationfalse;
no newmodule. Usage1793500028:76%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Current source, fixed semantics/ROM/dependencies remain unchanged.


## Current normal account image and provider suffix frames — 2026-11-01

The genuine current normal decode_account_from_leaf now supplies its full
physical56byte account image, including both real32byte references, from
its actual caught parser, list converter, count/type/length guards and four
field calls. Current.field_normal and fields_normal derive real values and
compose the current outside-high-scratch frame. Current.body_decode_prefix,
after_slices_fields, after_decode_fields and body_fields join those reached
states without the old cursor<=cutoff<=input premise. The real list result
and count guard force exactly64bytes of fresh record allocation below
2952790016. Zero length still has no invented pointer-order premise; normal
completion itself contradicts that case. Actual persistent input lower
bounds derive physical reference payload arenas independently of scratch.

Current.body_normal and ignored_normal retain the actual LiveArena,
metadata of the real heap-only64byte update, all earlier words outside the
56byte account output, and the already proved191*length+261body/262caller
allowances. Their empty-root/hash references are current typed globals with
physical arenas; these are helper-entry prerequisites, not new main premises.
The genuine main-to-provider producer connection for those prerequisites
still needs to be supplied. AccountDecodeTailGlobals now uses direct current
memory-metadata effects for memzero/output and derives the older individual
global frame from them. Its obsolete broad BufferGlobals dependency, which
pulled stale accelerator/table/VM catalogues, has been removed.

At the actual ws_get_account_optional suffix, after_alloc_normal connects
that real ignored caller to the literal returned account pointer.
after_guard_normal derives the actual56byte allocation room from execution,
then combines both allocations and real decoder writes into a
PersistentNormalFrame protecting every word before the incoming heap.
The actual after_leaf_normal classifies absence as sentinel1 with unchanged
nonlocal state and presence as the physical returned account plus that
allocation frame. These are the full suffix after ws_account_leaf, not the
complete provider/outer getter normal frame. The latter still needs the
actual hash/trie/read-recording earlier-memory interval, with genuine low
workspace writes excluded. In particular, do not claim an unmodified full
PersistentNormalFrame across ws_account_leaf's low hash/nibble writes.

Selected FreshTransactionMemory current-account-suffix-normal-v2.log
PASS3479,27.11s/peak2814788KiB. Registry2311modules/8869facts at6957805e;
incremental policy PASS65536entries/2490936483bytes; fixed revalidationfalse;
no newmodule. Usage1793500788:76%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next connect actual leaf/provider normal memory and initialized BS/TS/code
records, derive current empty references at their real producer if needed,
and continue first get_account/ext_code_of/get_code. Legacy AccountDecode
normal/cursor consumers outside these selected roots can still require the
current heap cap when reused. Current source, fixed semantics/ROM and
pinned dependencies remain unchanged.


## Whole leaf/provider normal frame and real pre-state suffix — 2026-11-01

The actual initialized trie lookup now has a shared lookup_normal_trace,
reused by the existing normal-value theorem and the new normal-frame theorem.
Its true child answer, nibble-only OutputFrame and real release continuation
come from the same scoped call. finish_normal_state derives the exact saved
mark release and returned lexical state. lookup_normal_frame retains runtime
metadata with that mark restored and every word at or above2701135464.

The complete normal ws_account_leaf frame is now checked through real
software hashing, trie lookup, heap mark, observed32byte allocation and
release. after_alloc_normal_frame protects the interval below its fresh
digest and after the low workspace. after_mark_normal_frame derives actual
allocation room, and body_normal_frame proves exact original metadata and
all memory words2701135464<=query<incomingHeap. The saved mark is derived
from the actual entering heap. Low hash/nibble workspace writes are allowed;
no full earlier-memory equality or cryptographic oracle is assumed.
Leaf.scoped_normal_frame carries the actual bounded initialized answer,
retained metadata/interval and genuine caller continuation through the ABI.

Optional.body_normal now joins that complete leaf frame to the complete
normal allocation/decoder suffix. It returns the real sentinel1 or physical
account image. AccountLookup.Frame retains the actual bounded advancing heap,
nonheap globals/runtime and the earlier interval above2701135464. This
weaker memory interval, rather than an unjustified full persistent frame,
is the reusable guarantee after low workspace changes. Frame.of_erase and
Optional.scoped_normal retain it across actual callee entry/local restoration.
PreStateAccount.after_record_normal connects the real recorded initialized
state, provider caller and literal final return, retaining the same real
account result and frame. Its current empty-root/hash scalar globals and
physical arenas remain helper-entry facts still needing their main producer.

Selected FreshTransactionMemory current-pre-state-provider-frame-v1.log
PASS3479,29.76s/peak2821572KiB. Registry2311modules/8881facts at6957805e;
incremental policy PASS65536entries/2490970532bytes; fixed revalidationfalse;
no newmodule. Usage1793501488:76%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next carry the genuine read-recording prefix's Recorded state through this
normal suffix and enclosing first account lookup. Retain that actual Recorded
entry plus AccountLookup.Frame when deriving the later code-lookup table/
database model; do not transport FreshTransaction.Context.older unchanged
through low hash writes (it asserts equality below its frontier). Derive the
current empty references from real startup/main if using these image contracts.
Then finish first get_account/ext_code_of/get_code and its real system caller.
Current source, fixed semantics/ROM and pinned dependencies remain unchanged.


## Whole first optional-account normal result and current empty constructor — 2026-11-01

The actual pre-state getter now has body_normal through its whole repeated
access write, block-cache miss, read recording, complete provider and final
return. to_after_record_references derives the real reached environment and
empty-reference cells from the original context and recording metadata.
AccountLookup.NormalResult retains the actual Recorded entry plus its
AccountLookup.Frame to the returned state, current hash/scratch environment,
empty-reference globals and genuine sentinel1 or physical account image.
It does not assert FreshTransaction.Context.older survived low hash writes.
NormalResult.of_erase preserves this model through actual caller scopes.
PreStateAccount.scoped_normal supplies it to the genuine continuation.

The complete unchanged first get_account_optional now has after_miss_normal,
body_normal and scoped_normal using that same model. Its actual initial
access/cache prefix and whole pre-state caller are included; the final
returned account and recorded state survive every real lexical restoration.
The same existing source-cost bounds198960pre-state/198992outer body remain.
No account cache fill is introduced or assumed.

References currently records the actual fixed empty_trie_root2701134640
and empty_code_hash2701134672 globals. Its helpers transport them through
real context/global/metadata frames. These are temporary helper-entry
prerequisites, not assumed additional main inputs: the main-to-account
producer for References remains open. Current Data already retains mptEmpty
but does not retain empty_code_hash. Derive that cell from the actual MPT
startup template and carry it through later initialization/input/main Data;
do not add an unproved main hypothesis or derive it from the other pointer.

Current acct_new/acct_empty normal bodies and their real scoped callers now
use the genuine2952790016allocation cap. Normal room/results and heap growth
are derived from the current allocator. AccountEmpty.body_persistent_frame
packages its actual fresh56byte account image and all-earlier-memory frame.
AccountObjectGeometry no longer imports the obsolete mutable-table registry:
the pure Output.slot_number fact moved unchanged into AccountImage, which
that registry itself imports. This removes the stale hash-map dependency
from these selected constructor roots without changing the guest program.
The unused legacy registry itself was not revalidated by these roots.

Selected FreshTransactionMemory and AccountEmptyCallNormal
current-first-account-empty-normal-v2.log PASS3486,37.25s/peak2879288KiB.
Registry2318modules/8906facts at6957805e; incremental policy
PASS65536entries/2490991539bytes; fixed revalidationfalse; no newmodule.
Usage1793501975:77%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next close References at actual startup/main (Data and its real producer),
then connect the required get_account sentinel/empty-constructor branch,
ext_code_of/get_code and actual system caller. NormalResult.recorded plus
its interval frame should derive the current BS/TS/code database model after
hash writes. The enclosing required getter already has its all-outcome cost
198997body/198998caller, but its normal image/frame is not connected yet.
Current source, fixed semantics/ROM and pinned dependencies remain unchanged.


## Empty account references derived from actual startup/main — 2026-11-01

The References entry requirement is now supplied by the actual main Data
producer. MptWorkspace.template_empty_code proves the real template cell
at cursor+32. first_four_complete exposes it from the same actual MPT
initializer return, and main_empty_code_cell derives2701134672 from the
real source-base initialization and unchanged later startup prefix.
main_decoder_empty_code_cell preserves that exact cell through the actual
decoder/root traces. No pointer value is inferred from another global.

WorkspaceFrameCore.WorkspaceKey and CurrentHash.Cursor now include the
empty-code-hash cell. Their existing real helper frames cover that key.
CurrentHash.Workspace retains it through actual hash invocation, root
allocation, callee entry and every request-hash body/caller. Data.mptEmptyCode
is produced by main_inputs from that same real returned workspace and
retained by the real frame/metadata/global helpers, database creation,
state_init, header construction, transaction-data and block/BAL paths.
Data.account_references extracts both typed reference cells at the actual
first-account input point. Existing generic account helper contracts still
take References, but their main producer is now proved; no additional main
hypothesis or replacement source implementation is introduced.

Selected current-empty-code-producer-v1.log PASS1884,331.32s/peak2143084KiB
for the actual startup/hash producers; FreshTransactionMemory
current-main-account-references-v2.log PASS3479,65.43s/peak2884776KiB.
Registry2318modules/8910facts at6957805e; incremental policy
PASS65536entries/2490998211bytes; fixed revalidationfalse; no newmodule.
Usage1793502847:77%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next connect AccountRequired's actual optional-return/sentinel branch to
the checked current AccountEmpty.body_persistent_frame. Its assigned call
updates the existing a local, so use CallNormal.local_data for that real
call, not an invented decCall. Extend the genuine NormalResult.recorded
interval frame with the actual persistent allocation, then carry the required
physical account to ext_code_of/get_code. Data now directly supplies both
AccountLookup.Environment and References. NormalResult.recorded plus its
interval frame should supply the later BS/TS/code database model after low
hash writes; do not restore the stronger obsolete full older-memory snapshot.
Current source, fixed semantics/ROM and pinned dependencies remain unchanged.


## Complete required-account normal return and real ext_code prefix — 2026-11-01

The actual get_account sentinel branch now uses CallNormal.local_data for
its assigned acct_empty call to the existing a local. empty_call_normal
extracts the actual constructor return,56byte persistent frame and new
physical image. Frame.after_persistent and NormalResult.after_persistent_image
extend the genuine recorded interval through this real allocation.
NormalResult.input_heap/block_lower derive the constructor entry frontier
from the actual recorded state and continuing heap, without future room.
The present branch skips construction and returns its real existing image.
AccountRequired.after_optional_normal and body_normal retain the actual
recorded state, workspace, references and account image on both branches.
Every actual normal required lookup returns a mapped physical account beyond
BS+80, never merely the absence sentinel. Its previously checked all-outcome
source cost stays198997body/198998caller.

The real Software ext_code_of is checked at index499. ExtCode.to_code
classifies its complete first required-account caller: either stop within
198998source ticks or reach the unchanged get_code continuation with the
actual normal account, recorded state and original addr local. ExtCode.Ready
owns the real image; Ready.code_arguments derives mapping of a+48 and the
actual stored scalar hash pointer from that same account. No hash argument,
physical output or later get_code call is assumed. Ready is a Type holding
its concrete account/image; the trace returns Nonempty Ready.

Source inspection correction: ws_get_code reads the real code database at
WS+16. WS+8 is the state_root field in state_init. Earlier WS+8 code-database
notes were wrong; use the actual Software AST. get_code still checks the
TS+48/BS+48 code caches and records the read at TS+40. WS+24 is the materialized
account-trie root and WS+32 is a separate initialized table.

Selected FreshTransactionMemory current-ext-code-account-entry-v2.log
PASS3486,33.16s/peak2876424KiB. Registry2318modules/8927facts at6957805e;
incremental policy PASS65536entries/2491020603bytes; fixed revalidationfalse;
no newmodule. Usage1793503421:77%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next derive current TS+48/BS+48 empty code-cache images and TS+40 empty read
record table from NormalResult.recorded plus its interval frame, then price
actual get_code and ws_get_code. Crucially StateInit.WorldState currently
retains only initialized BS tables and the WS+24 witness trie; it does not
retain a code-database image. Trace the genuine completed code-db builder
from main through WS+16 and initializer/header/read-recording frames; do not
assume a database from a typed WS pointer. Existing CurrentTable.NodeLookup
.Database is specialized to lengths<=1024 (node data), so its bounded-result
contract will need a genuine code-length<=65536 producer/generalization if
reused. Runtime query structure/actual read rows should be reused where valid.
Current source, fixed semantics/ROM and pinned dependencies remain unchanged.


## Genuine code database through state initialization and account return — 2026-11-01

NodeLookup.Database now has an explicit value-length cap, default1024 for
existing node clients. Main's genuine completed code builder supplies its
Patricia image and real decoded rows with cap65536. WitnessRows.rows_at
retains the actual copied-input lower frontier2701135464; the original
rows API remains available. HasTables.code_database derives the database,
its table ordering and real heap frontier from the observed builder result.
No database image is assumed from a typed pointer.

The actual state_init entry retains this database and little endian fact.
The real root/suffix frames expose preservation of WS+16, where state_init
stored its codedb argument. CodeWorldState extends the existing WorldState
with that actual database, its bound before WS and endian fact. Actual
header/main/transaction/read-recording snapshots now retain CodeWorldState;
the generic weaker WorldState API remains unchanged.

NormalResult.code_database composes the real recorded earlier-memory band
with AccountLookup.Frame across account hashing and allocation. It derives
the genuine code image, decoded rows, WS+16 cell, typed WS global and WS
arena at the actual returned account state. Database.of_interval preserves
only the needed input/database interval, accommodating real lower workspace
writes. The BS+80 endpoint uses the actual arena's no-wrap fact.

Selected FreshTransactionMemory current-account-code-database-v2.log
PASS3486,33.87s/peak2849632KiB; TransactionNonempty
current-code-world-consumers-v1.log PASS2964,2.98s/peak723476KiB.
Registry2318modules/8934facts at6957805e; incremental policy
PASS65536entries/2491033188bytes; fixed revalidationfalse; no newmodule.
Usage1793504674:78%, ordinary allowed, one reset credit remains.
No whole-main source allowance/global finite target K/full verifier; infinity.
Next derive actual TS+48/BS+48 empty code-cache images and TS+40 read-record
image from the real Recorded state and account interval frame, then price
get_code and ws_get_code using this genuine WS+16 database. After the real
TS+40 insertion, preserve the database with its actual scalar-write frame;
do not retain an unchanged full account interval across that write.
Current source, fixed semantics/ROM and pinned dependencies remain unchanged.


## Real code-cache misses and complete code-database wrapper — 2026-11-01

Recorded now retains cutoff<=record from the actual recording call's
existing before premise. NormalResult.layout derives BS+80<=cutoff<=record
and record+72<=the real fresh heap. Frame.empty_image protects real earlier
scalar headers within its proved interval, allowing low hash workspace writes.
NormalResult.transaction_tables and block_tables derive every still-empty
TS/BS table at the returned account state. No untouched full-memory snapshot
is restored. CodeLookup.transaction_entry/block_entry then derive the actual
mapped TS+48 (32byte keys,cap16) and BS+48 (32byte keys,cap64) loads and
query arguments from those images and their real record arenas.

The actual Software ws_get_code at index336 is now checked end to end.
World.Entry is supplied by NormalResult.code_database, including the real
WS+16 cell, WS global and arena. Its actual nodedb_lookup caller costs265;
its own opening32byte memeq caller costs129. World.body_cost<=394 and
World.scoped_trace<=395 include empty-hash fast return, missing-code StateErr2,
failed/malformed reads and clock-zero outcomes. World.body_normal returns
empty code or an exact row from the genuine completed code database, with
full nonlocal preservation. Entry.result_bound supplies length<=65536 and
a real input arena for every nonempty returned code. No hash-presence or
future helper success hypothesis is introduced.

CodeLookup.shapes checks the actual get_code syntax, including the distinct
assigned BS query to existing w (not a second scoped declaration). The TS
query's actual absent return is proved with scoped_scalar_empty_trace;
block_call_normal uses the real assigned call data and body_scalar_empty.
cache_miss removes only guards whose actual w is that literal absent result.
caches_miss_trace connects both genuine queries to the real sk_make suffix
within4source ticks, retaining the account/database snapshot and caller locals.
CodeLookup.to_key adds the actual initial memeq caller and empty-code guard:
every outcome either finishes within133source ticks or reaches that exact
suffix within133, with real NormalResult, original addr and code_hash locals,
and the full enclosing lexical-scope observation. Empty returns/errors/timeouts
are included. World.scoped_trace provides the checked downstream caller.

Selected FreshTransactionMemory current-code-to-key-v3.log PASS3487,
38.63s/peak2971812KiB. Registry2319modules/8965facts at6957805e;
incremental policy PASS65536entries/2491083888bytes; fixed revalidationfalse;
8745Solver modules, no newmodule. Usage1793505726:78%, ordinary allowed,
one reset credit remains. No whole-main source allowance/global finite
target K/full verifier; claim infinity. Current source/fixed files unchanged.

Next connect the genuine sk_make call and TS+40 first code-read insertion
before World.scoped_trace. Important source fact: sk_buf is NOT a fixed low
workspace pointer. state_init's scratch suffix allocates64 persistent bytes
for it after the initialized BS tables. Derive its actual global, arena and
position from that real allocation and preserve them through journal/main/
account execution; do not assume a buffer address from another workspace cell.
StorageKeyProgram/Execution/Normal still use legacy Guest sk_make/index328;
port the reused current helper to Software/index326 and validate its closure.
The code-read table is TS+40,key52/cap16, still genuinely empty above. Its
actual scalar insertion changes earlier retained memory: retain the code
database with the real write footprint rather than claiming unchanged full
NormalResult across the write. Then compose actual get_code and ext_code_of,
continue the mandatory system/EVM/block/main path and eventual target-step
transport/exact bound/slack review/cleanup/allowed-host full verification.


## Genuine key-buffer allocation reaches returned accounts — 2026-11-01

The actual state_init scratch suffix now supplies KeyBuffer: its real
sk_buf global,64byte mapped arena, alignment, position after BS+80 and
extent before the observed final initialization heap. journal_key_buffer_global
proves preservation by the unchanged journal suffix on every outcome.
Context.journal_normal_grows derives actual heap growth from the real
journal allocation; scratch_normal_key derives its64byte buffer room from
the real allocator return, never an assumed successful future request.
Existing weaker scratch/journal/table APIs remain projections of these
stronger producers. actions_normal_key and after_block_allocation_tables_key
carry the same fact through all real block-table initialization actions.

The actual afterTable/afterRoot frames and current_body_normal_complete
retain this buffer through real scoped restoration. CodeWorldState now
retains KeyBuffer alongside its genuine code database. state_init_normal_complete
constructs both from the same actual execution. RetainedRecords now also
retains the actual sk_buf global: from the genuine header StateFrame, through
block-environment/output allocations, stores, BAL setup, fresh state and read
recording. Each new equality comes from its existing proved global frame.
Recorded retains the original initialized heap cell as well as cutoff<=record.
NormalResult.key_buffer derives the actual buffer global/arena/alignment at
the returned account state, with BS+80<=buffer and buffer+64<=cutoff. No
extra main hypothesis was introduced; no full unchanged memory snapshot
is claimed across lower workspace writes.

StorageKeyProgram now selects actual Software sk_make at index326; its
execution/normal/cost closure checks against current code. Legacy helper
body uses at index328 have been removed from that catalogue. Its existing
physical-body bound12 remains conditional on its actual input/output arenas.

Selected exact roots FreshTransactionMemory and StorageKeyNormal:
current-account-key-buffer-v2.log PASS3490,73.23s/peak2917008KiB.
Registry2322modules/8980facts at6957805e; incremental policy
PASS65536entries/2491094338bytes; fixed revalidationfalse;8745Solver modules.
No whole-main source allowance/global finite target K/full verifier; infinity.
Usage1793506328:78%, ordinary allowed, one reset credit remains.
Current source, fixed semantics/ROM and pinned dependencies unchanged.

Next use the real sk_make suffix from CodeLookup.to_key with the newly
derived NormalResult.key_buffer. Avoid adding an address-arena hypothesis:
ExtCode.Ready has the actual hashArena, but its generic contract does not
yet supply an arena for addr. Existing Input.CopyAny.call_span_normal in
CopyAnyCost.lean gives an exact destination-span frame and unchanged caller
locals for a real normal memcpy without mapping/allocation assumptions.
CopyAny.call_cost prices actual literal20/32 copies on all outcomes, so a
Current sk_make contract can use those facts (uniform cost67 vs mapped12)
without strengthening main inputs. Preserve the code database before WS
and TS+40 header/table beyond cutoff with that real destination frame;
then connect actual52byte-key/cap16 first read recording (Set.scalar_empty_call_cost
cost CopyAny.price52+5=70, scalar_empty_call_frame normal footprint) and
World.scoped_trace395. Do not retain unchanged full NormalResult across
sk_make or the TS+40 insertion. Complete get_code/ext_code_of/system/block/
main and target-step transport, exact bound, slack review, cleanup and
allowed-host full verification remain outstanding.


## Complete real first code lookup and ext_code_of — 2026-11-01

StorageKey.Current.body_cost prices the genuine20/32byte copies on every
outcome (67body/68caller), without input mapping/arena hypotheses. Its
body_normal derives the actual scratch-pointer return and exact52byte
Copy32Span.Frame from both real normal memcpy calls. Existing mapped12
body API remains available. This avoids introducing an addr-arena premise
at the genuine get_code entry.

World.Entry now retains the actual completed database's bound before WS.
Entry.after_buffer and after_scalar preserve that genuine database, its rows,
WS+16/global/arena through the real disjoint key-buffer and read-table writes.
Uncached is produced by the same NormalResult: actual code database,
references/code, typed TS, mapped72byte record, TS+40 cell and empty52byte-key/
cap16 read table, positioned after the TS record and WS. It deliberately
retains only the needed facts across sk_make, not unchanged full NormalResult.
Uncached.after_buffer uses the actual initializer/recording ordering to
preserve the read-table header; read_arguments derives the actual mapped
TS+40 load and returned k. Real htab_set normal execution supplies its scalar
write footprint. The now-singleton read table is not claimed to remain empty.

All-outcome source allowances are now complete for the unchanged first
get_code: opening comparison/cache prefix133, actual key caller68, first
52byte read-record insertion70, actual ws_get_code caller395, total666body/
667caller. Source catalogue is Software get_code at index342. The actual
ext_code_of after-account suffix uses this caller with its real loaded hash
and restored address. Complete ExtCode.body_cost<=199665 includes the real
required-account caller198998 and get_code667, on all failure/timeout/normal
outcomes. No hash-presence or future successful call is assumed.

CodeLookup.Answer is the genuine returned pointer/length pair, length<=65536,
with a mapped arena for positive lengths (literal null empty code allowed).
after_read_normal derives it from World.scoped_trace and the real return;
after_key_normal and after_caches_normal follow actual setter/key calls and
frames. first_get_normal proves both genuine cache misses; body_normal also
handles the actual empty-hash early return. returning_normal carries this
through the real get_code caller/return local. ExtCode.after_account_normal
and body_normal derive the same bound through the actual required-account
and code callers. These are complete normal value results; they do not yet
expose a post-state registry/environment/heap frame for the later VM setup.

Selected FreshTransactionMemory current-complete-code-normal-v2.log
PASS3491,41.66s/peak2971692KiB. Registry2323modules/9006facts at6957805e;
incremental policy PASS65536entries/2491138391bytes; fixed revalidationfalse;
8745Solver modules, no newmodule. Usage1793507025:78%, ordinary allowed,
one reset credit remains. Current source/fixed files remain unchanged.
No complete system/EVM/block/main allowance, global finite target K or full
verifier; claim infinity.

Next connect actual UncheckedSystem.afterFresh ext_code_of caller using its
already checked fresh_transaction entry/data and the new ExtCode contracts.
Actual Software process_unchecked_system_transaction (index794) continues
with te_new, message setup and a30000000gas system execution, even for empty
code; do not invent an early empty-code return for this wrapper. Derive its
real scalar stores and bounded code/message entry from the same normal call.
Strengthen the new normal code result with needed environment/heap/global/
remaining-memory facts from its real span/scalar/readonly frames as needed;
post-state TS+40 is a singleton, so do not reuse old empty-table Context.
Continue the actual mandatory system/EVM/block/main proof and eventual target
transport/exact K/slack review/cleanup/allowed-host full verification.


## Real first system caller reaches environment setup — 2026-11-01

The complete CodeLookup normal stages now retain an exact MemoryMetadata
frame alongside Answer. The actual code helper changes memory but preserves
its incoming heap, globals, domain/endian and runtime settings. The first
cache trace now exposes its real full physical frame; the final ws_get_code/
return is proved readonly. Scalar read recording and the key write supply
their own strict metadata frames. Each actual normal caller/restoration
composes these facts. No unchanged full memory snapshot is claimed.

ExtCode.body_normal_complete retains the real returned-account snapshot
and the exact later code metadata frame. body_normal_context derives the
actual output's bounded code, AccountLookup.Environment, References and
bounded aligned heap>=BS+80 from that same snapshot. The earlier pure
ExtCode.body_normal remains a projection. This supplies real allocation
entry facts for later system setup without a new heap hypothesis.

UncheckedSystem.CodeState carries these real code/runtime/heap facts and
BS>=2701135464. to_environment follows its actual ext_code_of caller or
stops within199666source ticks. body_to_environment composes the genuine
fresh-state call, deriving cutoff<=record from its actual heap: within199741
body prefix ticks it either stops or reaches the exact te_new suffix with
CodeState and preserved original locals. first_to_environment instantiates
this at main's actual first system caller using Data.account_lookup_environment,
Data.account_references, the real InitializedRecords and after-header heap.
The actual first_entry classifies target/data words from the observed call,
so no typed beacon-address assumption was added. Continuing caller prefix
<=199742, with original target, pointer+26 data and literal32 data_n. This
is a prefix trace retaining its original continuation, not a whole-system
allowance or an assumption that future setup/message execution succeeds.

Selected FreshTransactionMemory current-first-system-environment-v2.log
PASS3491,45.44s/peak2996044KiB. Registry2323modules/9013facts at6957805e;
incremental policy PASS65536entries/2491155261bytes; fixed revalidationfalse;
8745Solver modules. Usage1793507803:78%, ordinary allowed, one reset credit.
Source/fixed files unchanged. No full system/EVM/block/main allowance,
global finite target K or full verifier; claim infinity.

Next port and connect the real te_new (200bytes) and msg_new (176bytes)
constructors, then their actual stores and table calls to process_message_call.
Existing Input/FreshRecord.lean and FreshRecordCall.lean already share both
literal constructor proofs, zero cells, canonical returns and outside-memory
frames. They still select legacy Guest constructors and give the allocator
room33806089496. Change reused constructor bodies to Software and use the
actual allocator cap2952790016 (do not add room as a main premise). Add the
actual source catalogue entries and revalidate this exact selected closure.
Existing Input.CurrentAlloc.scoped_classified (CurrentAllocationTrace.lean)
can derive room or a stopped outcome from the observed allocator call.
FreshRecord.execute with derived room and mapped arena gives exact9body/
10caller ticks; insufficient clocks are already bounded, and impossible-room
allocation stops within2. This can avoid a loose generic zero allowance.
CodeState.heap and lower derive the incoming owned aligned bounded heap.
Normal contexts for environment/message stores must follow their real calls,
not old GasBudget.MsgNewNormal's obsolete33806089496 cap or unvalidated
legacy system message assumptions. Complete VM/system/block/main, target
transport, exact bound/slack review, cleanup and allowed-host verification
remain outstanding.


## Current shared TE/message constructors and first TE allocation — 2026-11-01

Input.FreshRecord/FreshRecordCall now select the actual Software te_new
(index793,size200) and msg_new (index421,size176). Reused allocator-room
contracts use2952790016 instead of the obsolete33806089496. original_code
checks both actual catalogue entries; no guest implementation was changed.

FreshRecord.normal_room derives request room from the same actual allocator
normal call. body_cost<=9 covers every constructor outcome: with actual room,
the mapped aligned record and exact execute prove its9tick body; without room,
CurrentAlloc.scoped_classified forces a real stopped allocator within2ticks.
Insufficient clocks are included. body_normal derives room/funding and the
exact real return/post-state with clock padding, with no room premise at entry.
body_normal_complete supplies the owned record, every zero word, a genuine
PersistentNormalFrame and bounded aligned heap beyond pointer+size. The generic
scoped_trace costs10caller ticks and exposes that actual continuing record,
frame, extent, zero cells and caller locals for either constructor kind.

UncheckedSystem.CodeState.heap_pointer derives its ordinary owned cursor
from the actual BS lower bound and reached heap. after_persistent retains
bounded code/runtime/reference facts through an actual constructor and its
proved caller-local observation. EnvironmentState now owns the actual200byte
TE record, typed local, alignment, every zero word and heap>=TE+200.
environment_trace connects the real te_new call to its actual field-store
suffix or a stopped outcome within10ticks. first_environment_trace composes
main's real first caller/code prefix: stop or reach that exact suffix within
199752caller source ticks, retaining original target/data/pointer+26/32byte
input bindings and the real EnvironmentState. No future constructor success,
allocation room or message-state entry was assumed.

Selected FreshTransactionMemory current-system-environment-constructor-v1.log
PASS3493,46.81s/peak2994464KiB, including the ported FreshRecordCall closure.
Registry2325modules/9036facts at6957805e; incremental policy
PASS65536entries/2491176931bytes; fixed revalidationfalse;8745Solver modules.
Usage1793508613:79%, ordinary allowed, one reset credit retained.
Current source/fixed files unchanged; no whole-system/EVM/block/main allowance,
global finite target K or full verifier; claim infinity.

Next classify the actual five TE stores in afterEnvironment, then the real
msg_new caller and message stores/table allocations to process_message_call.
Those TE stores are at0(vm_system_address),8(target),48(BE+48fee,4words),
80(literal30000000gas),88(literal97920*16=1566720state gas). Price the actual
quiet store prefix at0 with CallPrefix actions/priced_frame_trace; a failed
read/store stops there, and only its actual continuing execution supplies
field facts. Its last two stores give the real gas words; preserve them through
the message constructor using the genuine heap>=TE+200 and its earlier-memory
frame. Preserve CodeState/runtime/heap and original caller bindings via the
actual stores' metadata/local frames; do not carry EnvironmentState.zeros
unchanged after overwriting fields. FreshRecord.scoped_trace .message already
supplies the176byte zeroed message and heap beyond it, at10caller ticks.
Do not reuse GasBudget.MsgNewNormal's unported old-cap assumptions.
Continue actual VM/system/block/main, target transport/exact K/slack review,
cleanup and allowed-host full verification.


## Actual TE stores, message allocation and message-field prefix — 2026-11-01

UncheckedSystem.Stores describes only literal store commands. Its fields
proof composes actual normal command executions to retain runtime metadata
and caller locals; its price is0source call/loop ticks including failed
operands/stores. environment_stores_shape checks the actual five TE stores.
environment_fields follows the genuine early3+last2 execution, derives the
literal30000000 execution-gas and1566720 state-gas words, and retains the
owned TE/heap/runtime context. PreparedEnvironment replaces the constructor's
old zero-cell assertions. environment_fields_trace reaches the actual msg_new
call or an earlier stopped store without assuming any operand succeeds.

The actual msg_new caller uses the already current shared FreshRecord proof,
cost10caller ticks. MessageState owns its real176byte zeroed record, typed m,
alignment and heap>=m+176. Its entering heap is proved>=TE+200 from the real
prepared state, so PreparedEnvironment.after_persistent preserves both actual
TE gas words through message allocation/clearing. environment_to_message and
first_message_trace compose the actual first main system caller through this
message constructor within199762caller ticks, retaining original target,
pointer+26 data and literal32 data_n. Stopped outcomes remain included.

ordinary_words_before proves that a normal arbitrary tuple store preserves
every earlier cell. It uses the exact mapped ordinary-domain upper end
33806089704 (CopyAny.ordinary_bounds), which prevents64bit address wrapping
between normal word writes. This is distinct from the conservative Arena
end33806089496 and the allocator cap2952790016. ordinary_store_before derives
the actual stored value/write list from execution; no value-shape/success
oracle is introduced. FieldStores retains that earlier-memory fact through
real record-field prefixes. environment_fields_memory applies it to the TE.

message_stores_shape checks the twelve actual message stores before the
first warm-account table. MessageState.after_fields uses their real metadata,
local and earlier-memory frames to retain TE gas/heap and code/runtime settings.
It does not retain the now-overwritten message zeros. MessageFieldsState
keeps the actual incoming MessageState and field execution for later scalar
word proofs. message_fields_trace and first_accounts_trace connect this
unchanged suffix to the actual htab_new(20,8) call, still within199762caller
source ticks. The message's own gas/code/input word conclusions have not yet
been projected from that retained execution.

Selected FreshTransactionMemory current-system-message-fields-prefix-v2.log
PASS3493,50.83s/peak3075880KiB. Registry2325modules/9058facts at6957805e;
incremental policy PASS65536entries/2491213043bytes; fixed revalidationfalse;
8745Solver modules, no newmodule. Usage1793510625:79%, ordinary allowed,
one reset credit remains. Source/fixed files unchanged; no full system/EVM/
block/main allowance, global finite target K or full verifier; infinity.

Next derive the actual message scalar words from MessageFieldsState.execution:
TE pointer8, literal gas40/state-gas48, input pointer88/length96 (first call32),
target24/32/104 and code pointer112/length120<=65536 from CodeState.code.
All message field offsets are increasing. A useful next generic helper can
split a store execution at one scalar write and use a lower-offset bound for
its tail (or direct ordinary_store_before) to preserve that word. Existing
FieldStores.memory_before only protects queries before the base; generalize
for a tail's minimum field offset if needed. Do not assume arbitrary stored
global values are scalar, nor carry old zero fields unchanged: normal tuple
stores are handled by the new ordinary-domain before-memory proof.
Then connect actual htab_new(20,8), store at m+152, htab_new(52,8), store at
m+160, skip and the real process_message_call caller. Use current ScalarEmpty/
geometry and actual normal allocation frames/room producers, preserving the
message/TE through tables allocated beyond m+176. Retain the source CodeState
runtime/global/heap facts and original input bindings. No future table image
or message-call success may be added as a main hypothesis. Continue VM/system/
block/main, target transport/exact K/slack review/cleanup/allowed-host verifier.

## Checked message gas, environment and code words — 2026-11-01

FieldStores now carries a minimum destination offset. Its actual normal-store
proof protects any earlier field, including arbitrary later tuple writes.
Stores.take and Stores.scalar_field split the real store execution at a
scalar write and retain its value through that bounded tail. No successful
expression/store or initialized memory is assumed at main entry.

MessageState and MessageFieldsState now derive the real m+8 TE pointer,
m+40 gas30000000, m+48 state gas1566720, and m+112/m+120 code pointer/length.
The length remains<=65536, with an owned code arena for nonzero length (the
empty0 pointer case remains separate). These are actual memory conclusions,
not added hypotheses. The input/target words and warm-table setup remain next.

Selected FreshTransactionMemory current-message-scalar-fields-v3.log PASS3493,
51.42s/peak3030664KiB. Registry2325modules/9067facts at6957805e; policy
PASS65536entries/2491222146bytes, fixed revalidationfalse,8745Solver modules.
Source/fixed files unchanged. No global finite target K/full verification;
claim infinity. Next: input/target fields, real warm-table constructors and
message/TE preservation, then actual process_message_call/EVM/system/block/
main, target-step transport/exact K, slack review and obsolete-code cleanup.

## Real first warm-account constructor — 2026-11-01

CurrentTable.New.scoped_scalar_empty_trace now exposes the genuine constructor
on every outcome: stopped work<=9caller source ticks, or the actual initialized
scalar table image, exact next heap, persistent earlier-memory frame, caller
locals and original continuation. Its body remains the original htab_new116;
all four allocation requests derive their own room from actual normal execution.

UncheckedSystem.accounts_trace applies that helper to the real htab_new(20,8)
suffix. The returned table lies beyond the entire176-byte message; the next
heap lies beyond the table's88-byte header and all backing allocations via
ScalarEmpty.geometry. Every query before the message end is retained, together
with the real code/runtime context and lexical scope. No future table image,
allocation success or message execution is a supplied entry hypothesis.

Selected FreshTransactionMemory current-system-warm-table-trace-v2.log PASS3493,
51.79s/peak3027008KiB; shared-constructor downstream checks also passed in v1.
Registry2325modules/9069facts at6957805e; policyPASS65536entries/2491228086bytes,
fixed revalidationfalse,8745Solver modules. Source/fixed files unchanged;
no global finite target K or full verifier, claim infinity. Usage79%, ordinary
allowed, one reset credit remains.

Next: derive original target/input words from MessageFieldsState.execution,
carry the proved message/TE scalar fields through this actual frame, store
m+152=aa, construct htab_new(52,8), store m+160=ak and connect the original
process_message_call caller. The whole first-system prefix is still explicitly
connected only through entry to the first table (199762ticks); accounts_trace
adds the separate actual9tick constructor step, not a whole system bound.
Then finish current VM/system/block/main costs and formal target-step transport,
evaluate exact K, review dominant slack, remove obsolete implementation and
shortcuts, and arrange the permitted full verification.

## Complete original first system-message setup — 2026-11-01

The real message-store execution now proves target words at24/32/104 and input
pointer/length at88/96, from the actual original caller locals. MessageWords
collects these memory conclusions with TE pointer8, gas40/state-gas48 and
code112/120. PreparedMessage retains that memory view after real later calls;
it does not pretend the old store execution ends after subsequent allocation.

PreparedEnvironment.after_persistent_locals factors the earlier m-specific
constructor frame; PreparedMessage.after_persistent and after_field retain
message/TE words through actual allocation and late field stores. field_table
uses physical allocation order to preserve a later table header through a
message pointer store. AccountSetup and WarmSetup retain both initialized
20/52-byte-key,8-slot table images, actual m+152/m+160 pointer cells, complete
backing allocation geometry, ordered regions and bounded live heap.

account_setup_trace and storage_setup_trace each cost<=9source caller ticks
including their real constructor/store (and the final skip). Stopped outcomes
are included. first_message_execution_trace composes the unchanged first
system-call prefix through both tables to its actual process_message_call
caller, with bound199780 and real target/input(pointer+26,length32) words.
No table image, future allocation/store/execution success or supplied normal
return condition was added at main entry.

Selected FreshTransactionMemory current-message-arguments-and-setup-v4.log
PASS3493,55.81s/peak3117612KiB. Registry2325modules/9084facts at6957805e;
policyPASS65536entries/2491261015bytes,fixed revalidationfalse,8745Solver modules.
Source/fixed files unchanged. No complete process_message_call/EVM/system/
block/main source allowance, global finite target K or full verifier; infinity.

Next derive the actual process_message_call ABI/entry from this reached
message/table state; original Software signature is msg:one and first allocates
and zeros a96-byte output record. Preserve required physical world/account/
code/table images and typed BE/system globals from their genuine earlier
producers, strengthening actual normal frames where needed. Unknown global
store operands and the overwritten message zeros must not be assumed scalar
or retained. Follow the real nonzero-target message branch and frame setup,
complete VM/system/block/main costs, formal target transport/exact K, dominant
slack review, obsolete implementation/shortcut cleanup and permitted verifier.

## Actual message-call entry and output initialization — 2026-11-01

MessageExecution.original_code checks the unchanged Software
process_message_call559/msg:one signature. Memory separates the proved physical
message/TE/table data from system-caller locals; memory_of_warm and
call_environment derive the actual callee entry after its local reset. This
retains the genuine runtime/reference globals, both heap lower bounds, table
images, region order, message gas/code/input words and TE gas fields.
Memory.of_erase and after_persistent preserve this model across actual frames.
No future call result or normal-return condition is an entry hypothesis.

prefix_shapes checks the actual skip/alloc96/memzero sequence. allocation_trace
derives room from the real allocator, stops within2source ticks or reaches
its original memzero after1tick with owned/aligned96bytes and a heap beyond
it. OutputAllocated retains the genuine entering model/cursor and allocation
frame so clearing the new record does not incorrectly treat it as above the
advanced current cursor. OutputAllocated.after_clear combines that real frame
with normal memzero's exact bounded write, protecting earlier tables/message.
The resulting OutputReady derives every zero word from actual zeroing.

body_to_dispatch proves the whole initial output allocation/clear prefix costs
<=5body source ticks on all outcomes, or reaches actual afterClear with the
ready output and entry memory retained. Allocation traps, zeroing failures and
timeouts are included. No complete message/frame/VM cost is claimed.

Selected FreshTransactionMemory current-message-execution-entry-v4.log
PASS3493,59.95s/peak3100292KiB. Registry2325modules/9094facts at6957805e;
policyPASS65536entries/2491282778bytes,fixed revalidationfalse,8745Solver modules.
Source/fixed files unchanged, claim infinity; no global finite target K/full
verifier. Usage1793512801:79%,ordinary allowed,one reset credit remains.

Next continue afterClear's real frame=0 declaration and recipient branch into
process_message/process_create_message as dictated by actual memory. Do not
assume the first target is nonzero without deriving the real beacon-address
global, and do not assume message depth/flag zeros or typed BE/system globals
from a generic normal tuple store. Derive additional actual input/global/table
frames when needed (the old code/read-cache context cannot be treated as still
empty). Complete frame/VM/system/block/main source costs, formal target-step
transport/exact K, dominant-slack review, obsolete-code cleanup and permitted
full verification. The whole first-system prefix is connected to the message
caller at199780; the new5tick callee prefix is separate until later caller/body
composition, not an asserted complete system/main allowance.

## Checked recipient selection and complete message output tail — 2026-11-01

Stores.price_tail composes literal zero-source-tick stores with a priced
continuation. MessageExecution.dispatch_shapes identifies the actual frame=0
declaration and recipient guard. Entry.recipient_read/test/branch derives the
original create/process_message choice from the real m+24 word, without an
incoming nonzero-target hypothesis. OutputReady.of_erase and frame_entry_trace
retain the ready record and memory model across the actual frame declaration.
body_to_selected_call connects the original allocation/clear prefix through
that declaration/guard within5body source ticks on all outcomes.

The complete post-frame output assembly afterFrame now has source allowance1
on all outcomes. The only charged call is the original frame_state_gas_used407;
its actual declaration/arithmetic/return body costs0, and its caller costs1.
All other original output stores, signed refund adjustment, tests and return
are quiet. No readable frame/output, helper success or normal return is an
entry premise for this tail cost. Target straight-line work is still separate.

Selected FreshTransactionMemory current-message-dispatch-and-tail-v3.log
PASS3493,61.66s/peak3199008KiB. Registry2325modules/9107facts at6957805e;
policyPASS65536entries/2491295873bytes,fixed revalidationfalse,8745Solver modules.
Source/fixed files unchanged. No whole message/VM/system/block/main source
allowance, global finite target K or full verifier, claim infinity.

Next enter actual process_message540 (or prove the real beacon target is
nonzero before excluding create). Its initial read-only depth guard bounds
any continuing depth by1024, then it declares parent/parent_cont and calls
frame_open530 with(msg,0). Derive those facts from actual prefix execution;
never assume message depth/flag zeros from arbitrary global tuple stores.
Existing GasBudget.FrameNew* exact proofs may be reusable: current frame_new423
still allocates/clears280bytes,1024byte stack/memory, real jump bitmap, log list,
scratch table and warm counts. Check body/helper equality to Software, mapped
arena/room and real code/message/table/empty globals before reusing them.
Existing execute_full assumes typed evm_empty and explicit room/mapping/code;
these are not yet all derived by the current Memory model. Retain/derive real
world/table/global invariants instead of adding future-success assumptions.
Continue VM/system/block/main, target transport/exact K, dominant-slack review,
obsolete-code cleanup and permitted full verification.

## Actual process_message depth/parent prefix — 2026-11-01

ProcessMessage.original_code checks current Software process_message540 and
call_environment binds its real msg:one ABI from the proved message memory.
The actual prefix is the depth guard, skip, parent/parent_cont declarations,
then frame_open530(msg,0). prefix_cost and prefix_memory prove that prefix
adds no source ticks and preserves every nonlocal runtime/memory field,
including failures and lexical exits.

depth_guard_normal derives the real m+128 scalar word and bound<=1024 from
this actual continuing guard; no incoming zero-depth/valid-depth hypothesis
is assumed. prefix_facts uses the real execution's skip_erase observation and
local-binding frames to retain Entry, both tables and the same depth word at
the real open caller. body_to_open includes stopped outcomes or reaches that
original frame_open call with these derived facts.

Selected FreshTransactionMemory current-process-message-depth-prefix-v2.log
PASS3493,62.53s/peak3176208KiB. Registry2325modules/9115facts at6957805e;
policyPASS65536entries/2491305627bytes,fixed revalidationfalse,8745Solver modules.
Source/fixed files unchanged. No whole process_message/frame/VM/system/block/
main source allowance, global finite target K or full verifier; infinity.
Usage1793513827:80%, ordinary allowed,one reset credit remains.

Next strengthen the genuine startup/global producer facts before applying
existing whole-frame proofs. A read-only source comparison found exact text
matches between Guest/Ast.lean and Guest/SoftwareAst.lean for frame_new,
frame_open, compute_jumpdests, scratch_alloc, frame_mem_alloc, lst_new_scratch,
htab_new_scratch and htab_count. This is discovery evidence only; prove/check
actual Software catalogue/body equalities before formal reuse. The old
GasBudget.FrameNew.execute_full needs actual evm_empty word, mapped separated
input/table fields, arena room and code. The current entry already supplies
code-length<=65536, gas/reservoir, m+152/m+160 tables and empty header counts;
initial scratch/frame cursors are genuinely fixed. Current Memory does not
yet retain the typed evm_empty/vm_system_address/global-address facts.

Important existing producers to inspect: Input/OriginalScalarGlobals.lean
checks all67original scalar globals at declaration and has Scalars.update;
Input/MainEvmInitialization, MainEvmAddress, MainEvmFinal and MainForkAddresses
use Scalars. CurrentStartup.EvmInit, NormalHost, WorkspaceFrameCore and related
modules already check current initializer effects but retain only selected
workspace/cursor facts. Data in CurrentVerify/RunInputs currently drops the
extra globals; its actual source producer/forward frames may need strengthening.
Actual evm_init assigns vm_system_address via alloc24 (SoftwareAst17435) and
evm_empty via alloc8 (17449); fork_init allocates beacon_roots_address24 at32546.
Do not assume these globals are scalar simply from the existing Memory model.
Derive/retain their producer facts, then bridge current frame constructors,
continue VM/system/block/main, target transport/exact K, dominant-slack review,
obsolete-code cleanup and permitted full verification.

## Scalar globals derived through the complete current entry pipeline — 2026-11-01

The pinned core semantics already proves
evaluateHOLFiniteState_global_shape_invariant: every actual outcome retains
the shapes of existing globals, because each global write checks its old
shape. OriginalScalarGlobals.Scalars.after now applies that theorem to the
67declaration-derived scalar globals. Scalars.of_frame/of_heap_frame/prefix
cover real local frames, concrete word-valued heap updates and reached lexical
executions; evm_names checks the three actual EVM/address names.

CurrentStartup.ArenaState now carries this already-derived scalar property.
Main's existing memory_scalars supplies the real initial cursor state; actual
initializer/decoder/hash executions and normal allocation/table/trie/header/
withdrawal/block/transaction frames retain it throughout the current entry
pipeline. All affected runtime constructors now supply their genuine scalar
proof. Helpers that allow arbitrary replacement globals (Data/AfterHeader/
ReturnList.with_globals and ReturnList.of_memory_frame) explicitly retain
target scalar types, and actual callers prove that condition from the same
execution, returned runtime or concrete scalar update. No new hypothesis was
added to Main.Entry, the challenge or the final fixed statement.

MessageExecution.Memory.empty_global/system_global now derive actual word
bindings for evm_empty and vm_system_address at the reached message entry.
This closes the previously missing typed-global condition for old frame_new
proof reuse. It does not assert a nonzero beacon target, zero parent frame,
zero message depth, or any particular empty-buffer pointer value.

Selected FreshTransactionMemory plus ArenaEffects roots:
current-runtime-scalar-globals-v7.log PASS3494,62.14s/peak3184632KiB. The broad
v6dependency check also passed3493jobs. All40edited Lean modules lie in these
selected source import closures (ArenaEffects required the second root).
Registry2325modules/9122facts at6957805e; policyPASS65536entries/2491315032bytes,
fixed revalidationfalse,8745Solver modules. Source/fixed files unchanged;
claim infinity. No complete frame/VM/system/block/main source allowance,
global finite target K or full verifier. Usage1793516814:81%,ordinary allowed,
one reset credit remains. Failed/interrupted earlier port logs were not indexed.

Next bridge actual frame_open530/frame_new423 and their unchanged helper
bodies to the existing GasBudget.FrameNew proof library. The actual prefix
now supplies the typed empty global through Memory.empty_global; do not keep
treating that fact as an unproved new entry hypothesis. Derive mapped arenas,
room from the genuine initial scratch/frame cursors and code length<=65536,
protected message/table fields and empty warm counts from the current memory
model. Source text equality was observed earlier for the eight frame helpers;
formal Software catalogue/body equality is still required before reuse.
execute_full's enough-clock condition can support an all-outcome bound by
pricing shorter clocks directly; never assume future helper success.

Frame allocation changes scratch/frame cursors, so its post-state must not
falsely retain CurrentStartup.ArenaState's fixed initial cursor values. Carry
the generic scalar fact separately into a VM model with actual dynamic cursors.
Use genuine normal frames for the world/cache state; the read cache after code
lookup is not empty. Derive exact message zero fields or actual parent/target
values when needed instead of assuming them from the former weaker models.
Continue VM/system/block/main, target-step transport/exact K, dominant-slack
review, obsolete alternate implementation/shortcut cleanup and permitted full
verification. No new modules or guest-program changes were introduced here.
