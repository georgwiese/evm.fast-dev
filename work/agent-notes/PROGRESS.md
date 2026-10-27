# Current proof progress — 2026-10-27

Active plan: [bound.md](../../bound.md). Reference main:
`f892870c8682517186860842a3ff5f0dea1aa3eb`; actual Software AST.
**No global finite target K yet**; claim infinity; no complete verifier run.

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

Next real out/z32/si/error lexical prefix and decoder success/failure join, plus
normal-startup host and heap frontier facts. A skip sink inside lexical declarations
restores those locals before an external continuation, so do not extend the simple
sequence append identity across those scopes. Reuse CallPrefix.Execution/Reaches;
its existing Stopped classification tracks only outcome/clock, so add a nonlocal
frame classification before using it to transfer stopped-path globals/memory.
Then actual scratch cursor transport/covered terminal-outcome classification;
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
