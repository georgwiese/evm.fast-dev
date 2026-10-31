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
The complete while-loop theorem remains open.

The current finish Entry uses the earlier-input value layout needed by the
indexed serializer. Its actual update caller must retain those value bounds.
Later serializers with freshly allocated values need their genuine value
separation/layout facts too. Initial all-node populated-cache caps are still
producer obligations; a local normal finish's new byte count<=2952790016 follows
from its observed heap, not a numerical target for K.

## Remaining plan

1. Initialize PreparedStack from the first real begin. Preserve it through the
   actual push prefix, child begin and child-selection index stores. Retain
   graph membership, values/paths, cache bounds, live scratch arena, heap and
   caller locals in the same concrete loop state. Pop's local proofs are ready.
2. Prove the complete current ranked serializer while-loop on all outcomes,
   then its actual scratch-release/return and node_rlp/node_hash/root callers.
   Derive helper conditions from reached executions, never future returns.
3. Connect real initial all-node cache bounds, indexed-loop heap limits and
   value bounds through current updates. Complete actual nonempty transaction
   and withdrawal trie wrappers and their main/header callers.
4. Finish current table/pre-state/system-call/VM/finalization execution and
   complete main, preserving covered rejection/trap and accepting-output cases.
   Reuse old proofs only after revalidation against mapped scratch behavior.
5. Complete uniform source-to-target transport, include straight-line work,
   evaluate explicit K and review dominant slack. In particular distinguish
   actual uncached hash work from cached fast paths; consider charging genuine
   first hashes to advancing persistent allocations rather than multiplying a
   worst-case cache length by every child call. Do not optimize the guest.
6. Remove unused alternate Pancake implementation code, obsolete flat-only or
   empty-input shortcuts and dead proof dependencies. Recheck the final theorem,
   permitted axioms, fixed-file integrity and submission isolation requirements.
   Arrange final verification on an allowed host; report its actual scope.

## Checkpoint and reproducibility

Latest selected check: `current-fill-pop-stack-v2.log`, PASS1532jobs, permitted
printed axioms. Incremental policy PASS65531entries/2489326786bytes; full fixed
policy revalidationfalse. Inventory8740Solver modules, replacement AST reverse
closure0, frozen6957 files unchanged. Registry2143modules/6925printed facts at
6957; historical8700/19844 is not whole-current validation. Five package-entry
slots remain. Usage last observed59%, zero reset credits, ordinary usage allowed.

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
