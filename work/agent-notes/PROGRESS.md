# Current proof progress — 2026-10-27

Active plan: [bound.md](../../bound.md). Reference main:
`f892870c8682517186860842a3ff5f0dea1aa3eb`; actual Software AST.
**No global finite target K yet**; claim infinity; no complete verifier run.

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
