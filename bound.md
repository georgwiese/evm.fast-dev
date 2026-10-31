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
from its selected outer row and previously allocated record slot. Full outer
loop normal transitions, loop allowance and whole decoder setup remain open.

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

## Remaining plan

1. Complete the actual nonempty versioned-hash checker from its decoded
   transaction rows. decode_transaction itself still needs its source proof; its five item-field
   readers and both complete numeric readers are now checked. The actual blob
   decoder now has its complete linear cost and normal physical return; finish
   the other nested list decoders, then
   compose the transaction decoder.
   Replace VersionedHashes zero-only body/caller frames and later
   BlockExecution's empty-count declaration shortcut. The complete current
   header and actual run_attempt/header prefix are now checked; later
   TransactionData and BlockExecution clients are still unvalidated.
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

Latest selected check: `authorization-iteration-cost-v1.log`, PASS1414jobs
(complete actual six-field suffix cost/normal physical effects/index advance,
real assigned fourth caller and complete actual iteration allowance), permitted
printed axioms. Complete blob decoder check remains `blob-body-normal-v2.log`,
PASS1411jobs; complete header/main-prefix check `header-main-entry-v1.log`,
PASS3319. Incremental policy PASS65534entries/2489762239bytes; full fixed policy
revalidationfalse. Inventory8743Solver modules, replacement AST reverse
closure0, frozen6957 files unchanged. Registry2161modules/7522printed facts
at6957; historical8703/20101 is not whole-current validation. Two package-entry
slots remain. Usage last observed66%, zero reset credits, ordinary usage
allowed at1793465096.

Detailed chronological proof history: `work/agent-notes/PROGRESS.md`.
Reproducible evidence: `proof-checks.json`, `policy-check.json` and
`original-plan-inventory.json` in that directory. Failed builds are not indexed.

Use exact selected Lean roots only, artifact cache disabled, two workers and
the8GiB resource guard. Freeze candidate edits during builds/policy checks.
Do not run the full verifier, Solution root or an unqualified full build here.
After a successful selected build, record its log basename, regenerate inventory,
run incremental policy and git diff --check. Commit concrete checked work and
immediately push each commit to georg with the existing private push helper;
verify clean local/remote agreement. Never print that helper, .bashrc or tokens.
Check account usage periodically; account resets, not context resets, were
requested. No reset credits are currently available.
