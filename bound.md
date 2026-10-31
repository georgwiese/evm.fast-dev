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
continuation. The current ranked witness materializer costs<=1757412483170;
complete state_init<=1757412483565 under its derived physical entry conditions.
Main through complete state_init costs<=1760801932784. Later main is not connected.

The indexed setter and complete indexed loop now retain a supplied pure
value property through the real key conversion, insertion, header store,
counter advance and lexical return. The actual transaction decoder/entry
derives both pointer+length<=boundary and, for nonempty values, pointer>=
2701134824. PhysicalHeader.transaction_entry_owned supplies those facts to
the genuine builder ABI; setup and the complete loop retain them as Values.
Their source allowances remain36826 per iteration and36827*count for the loop.

The serializer has a real48-byte scratch-frame entry, bounded child selection,
actual normal push and initial traversal-rank arithmetic<=521215. All three
finish node kinds now have full local body cost/normal-result proofs and a
checked actual caller. Their real size decisions, allocations, writes, child
hashes, node cache stores and lexical restoration are retained. Body allowances:

- Branch:704*(cacheLimit/136)+CopyAny.price(valueLimit)+11906.
- Leaf:CopyAny.price(compactLength)+CopyAny.price(valueLength)+75.
- Extension:CopyAny.price(compactLength)+44*(cacheLength/136)+792.

The caller adds one source tick. These are physical-entry contracts, not a
complete serializer or target bound. Saved preparation records now come from
actual begin results, including exact size/first-byte decisions and compact
allocation geometry. Finish additionally preserves the real older persistent
band between the registered-node frontier and incoming heap, plus high scratch.
PreparedStack retains every active frame's saved descriptors and sizing facts
through an actual child finish. The real normal pop now reads its saved parent,
installs that parent as top, retains older headers/preparations, derives the
actual next bounded aligned heap and strictly decreases the traversal rank.
Initialization now derives the singleton prepared stack from the actual first
begin and top declaration. Actual push preserves every older preparation and
adds its genuine new record, with observed bounded aligned heap growth. The
complete selector, including extension and branch index stores, retains linked
headers and all saved preparations while updating the actual bounded head
index. Its actual child/found result now supplies registered membership and
positive nonnull/nonhash descent, including the extension's real post-index
child load and needs-RLP decision. Shared Persistent data keeps registered-node
and full-path frontiers fixed while transporting graph, values, paths, populated
cache caps and hash workspace through actual selection, push/new begin and
finish. Its begin/finish entry constructors use those same current facts.
LoopState joins those facts with the live scratch arena, actual top and
original registry. Normal while exit retains the original root's exact buffer,
byte count, alignment and extent below the observed next heap. The complete
body/caller normal proofs now preserve that sized root cache and the full
original registered trie, restore the original scratch arena and caller locals,
and derive every successful stage from the actual execution.
They now also retain the actual original input band through every push,
selection, finish, complete loop and cleanup. Preservation composes exact
input-memory equality and globals other than heap/scratch; the real restored
scratch cursor supplies the full nonheap-global frame for callers.

The allocated hash workspace places nodes/paths above the heap floor. Thus
stored paths, prepared compact copies and new encodings fit the251658240-byte
persistent heap window. Every while outcome costs at most
`(stepPrice(C,V)+1)*initialRank`, with initialRank<=521215 and
`stepPrice=32+max(251658240/2+29,finishPrice)`. finishPrice takes the maximum
of the actual three finish caller allowances, with compact copies capped by
that window. Complete fill body price is
`3+(251658240/2+27)+(stepPrice(C,V)+1)*521215+1`; the actual caller adds1.
At C=251658240,V=268435456, checked arithmetic gives858256814537851 body
source ticks and858256814537852 caller ticks. Instantiation still requires
actual initial cache/heap producers; these are local source results, no global K.

CurrentTrieRoot now replaces the obsolete low-scratch failure arguments.
node_rlp has complete cached/uncached body and caller prices plus a genuine
normal pointer/length result with retained registry, heap, scratch and input
state. Its actual scoped caller retains that pair and the same input/global
preservation, ready for node_hash's real continuation.
node_hash prices the real RLP return, allocation, software Keccak and cache
store, including cached-hash roots. Its complete normal body and actual scoped
caller now return the genuine nonnull scalar pointer, bounded aligned heap,
input-before-heap fact, original input band and every nonheap global. Real
allocation room, hash return and cache footer are extracted from the same run.
mpt_root prices empty and nonempty branches, actual hash/copy and its real
caller. Its complete normal body and ignored caller now return zero with
the actual bounded aligned heap, every nonheap global and caller input.
The real32-byte copy is framed independently of hash-buffer ownership;
its owned aligned output is below the protected input band or after it.
The caller's protectedEnd may be earlier than the serializer's value inputEnd.
Root body price is
`NodeRlpFill.bodyPrice(C,V)+CurrentKeccak.Hash.bodyPrice(C)+48`; at the same
window/input caps it evaluates to858256895957420, caller858256895957421.
Root entry requires each nonzero root to be nonhash or have a populated hash
cache. The actual indexed/root producers remain to connect; complete normal
root frames are checked, with no empty-only root conclusion in this module.

The checked serializer contracts now match main's input/workspace order.
Branch/path finish, shared Persistent and actual begin/fill transitions retain
value extent plus the nonempty pointer lower bound. Child hashing protects
2701134824<=query<inputEnd, with Keccak state/pad ending before2701134824 and
inputEnd before the node frontier. The single-byte backing-word decision has
the same derived bounds. The full root/fill cost formulas still check.
The real indexed update supplies this value interval. Later serializers with
freshly allocated values need their
genuine separation/layout facts too. Initial all-node populated-cache caps are still
producer obligations; a real completed encoding's byte count<=251658240
follows from its actual allocated heap window, not a numerical target for K.

## Remaining plan

1. Connect actual indexed/root producers to the checked current root
   contracts. Replace CurrentIndexedSetup's stale empty-only conclusions and
   old Root.Entry uses; those clients have not been revalidated at6957.
   Complete fill/node_rlp/node_hash/root normal frames and actual callers
   are checked; derive their physical entries from the real builder execution.
2. Connect real initial all-node cache bounds and indexed-loop heap limits;
   consume the retained borrowed-value bounds. Complete actual nonempty transaction
   and withdrawal trie wrappers and their main/header callers.
3. Finish current table/pre-state/system-call/VM/finalization execution and
   complete main, preserving covered rejection/trap and accepting-output cases.
   Reuse old proofs only after revalidation against mapped scratch behavior.
4. Complete uniform source-to-target transport, include straight-line work,
   evaluate explicit K and review dominant slack. In particular distinguish
   actual uncached hash work from cached fast paths; consider charging genuine
   first hashes to advancing persistent allocations rather than multiplying a
   worst-case cache length by every child call. Do not optimize the guest.
5. Remove unused alternate Pancake implementation code, obsolete flat-only or
   empty-input shortcuts and dead proof dependencies. Recheck the final theorem,
   permitted axioms, fixed-file integrity and submission isolation requirements.
   Arrange final verification on an allowed host; report its actual scope.

## Checkpoint and reproducibility

Latest selected check: `root-normal-v1.log`, PASS1535jobs, permitted
printed axioms. Incremental policy PASS65531entries/2489525801bytes; full fixed
policy revalidationfalse. Inventory8740Solver modules, replacement AST reverse
closure0, frozen6957 files unchanged. Registry2144modules/7045printed facts at
6957; historical8700/19959 is not whole-current validation. Five package-entry
slots remain. Usage last observed62%, zero reset credits, ordinary usage allowed.

The detailed chronological proof history remains in
`work/agent-notes/PROGRESS.md`; earlier versions of this plan remain in Git
history (before this cleanup, e41806054). Reproducible evidence is indexed in
`work/agent-notes/proof-checks.json`, `policy-check.json` and
`original-plan-inventory.json`. Failed builds are not indexed.

Use exact selected Lean roots only, with artifact cache disabled, two workers
and the8GiB resource guard. Freeze candidate edits during builds/policy checks.
Do not run the full verifier, Solution root or an unqualified full build here.
After a successful selected build, record its log basename, regenerate inventory,
run incremental policy and git diff --check. Commit concrete checked work and
immediately push each commit to georg with the existing private push helper;
verify clean local/remote agreement. Never print that helper, .bashrc or tokens.
Check account usage periodically; account resets, not context resets, were
requested. No reset credits are currently available.
