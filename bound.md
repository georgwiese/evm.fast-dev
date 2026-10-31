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

1. Complete actual nonempty withdrawal encoding/trie and main/header callers,
   retaining the real borrowed-value interval and workspace/output separation.
   Transaction builder/caller and its header prefix are now checked. Remove
   Withdrawals.BeforeRequests transactionsZero/withdrawalsZero and downstream
   uses in TransactionData/BlockExecution; they are stale empty-only shortcuts,
   not facts available on current main.
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

Latest selected check: `indexed-transactions-v1.log`, PASS3310jobs (complete
indexed builder, actual transaction caller and header continuation), permitted
printed axioms. Incremental policy PASS65531entries/2489602353bytes; full fixed
policy revalidationfalse. Inventory8740Solver modules, replacement AST reverse
closure0, frozen6957 files unchanged. Registry2148modules/7106printed facts at
6957; historical8700/20009 is not whole-current validation. Five package-entry
slots remain. Usage last observed64%, zero reset credits, ordinary usage allowed
at1793459855.

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
