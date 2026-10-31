# Current proof progress — 2026-10-31

Active plan: [bound.md](../../bound.md). Reference main:
`6957805e26f4bb44ef756406a2bd14d56cf89b92`; actual Software AST.
Scratch-domain proof port in progress: scratch is now ordinary mapped memory.
**No global finite target K yet**; claim infinity; no complete verifier run.
Previous effort estimate: **55%, plausible45–65%**, relative to old main
`f892870c`. This estimate and the complete-prefix bounds below have not been
revalidated for the new reference. Several old proofs depended on scratch
stores failing; current main allows those paths to continue. Historical
module/fact counts do not measure the work needed to port them.

## Historical milestones on f892870c, pending revalidation

The unchanged main prefix now reaches its actual execute_block call within
534124484749source ticks, with the real decoded input/header and allocated
block environment. Header encoding, hashing, validation and their actual
caller connections are checked. The executor initialization then either
stops within161source ticks or reaches the original first mandatory system
call with its physical input/output state and initialized BAL tables.
The actual initialized ws/bs record context and earlier state memory now
survive the complete header construction/validation and executor setup
through its first mandatory system-call entry.
Mandatory system calls, finalization, complete main termination and the
uniform formal target-step bound remain open. Source clocks are not target K.

## Complete actual header-validator cost, normal return and caller trace

The unchanged Software validate_headers212 now costs≤51528322body ticks and
≤51528323ordinary caller ticks on every outcome from its current physical
entry context. The count guard, both real allocations, all≤256header decode/
store/software-hash iterations and parent-link comparisons are included. Each
header row is genuinely≤1024bytes; the first iteration costs≤201152plus its
loop tick, and each link costs≤129plus its loop tick. Failed reads, guards,
allocation, comparisons, hashing and timeouts are covered. Source clocks still
omit straight-line target instructions.

Actual normal returns derive the allocated hs/hash tuple, count≤256, real
allocation geometry and next bounded aligned heap. The entire fixed input/row
region, software hash workspace and every nonheap global survive. Real scoped
call traces either charge stopped work or retain that genuine returned tuple,
physical next context, forward/paid clock and exact original continuation.
No future allocator/comparison/hash success is a supplied premise.

Cleanup separates actual validator syntax, physical row model, pure protected
input frames and memeq formals/ABI from old mapped-arena/normal-execution proof
umbrellas. The existing unchanged memeq body is checked against the current
Software code entry. Generic loop/control helpers use direct core facts or
explicit binding imports instead of incidental transitive imports; two scoped
control facts are now independent of the host-memory type.

Validation: current-header-validation-complete-caller-main-v2.log PASS2131jobs,
permitted printed axioms, including original main/root/header entry and the
moved memeq ABI/old runtime compatibility. Index8379modules/16920facts;
inventory8423/replacement closure0/frozen main unchanged. Incremental policy
65202entries/2483983435bytes PASS. No global finite target K/full verification;
claim infinity. Next: derive real startup Keccak workspace globals and physical
header row context from main, then later current paths/target composition.
Usage9%weekly/0resetcredits;8GiBguard/twoslots/cachefalse.

## Complete actual Keccak memory frame and caller

The whole unchanged Software keccak25692 now protects every word outside its
actual200-byte state,136-byte padding and32-byte output buffers. The proof
exposes every real normal zero/copy/block/pad-byte/final-absorb/output prefix;
the actual block exit derives the short remaining input extent. Both output
branches derive their real store/copy widths. A normal caller retains caller
locals, current workspace, immutable fields and every global, including heap.
No cryptographic output oracle or future successful execution is supplied.

Current entry conditions are actual installed code/domain, workspace globals/
allocated geometry/alignment, physical input/output extents and typed arguments.
Connecting the actual startup workspace values and retaining them through main
is still separate; no global finite bound is claimed from this helper theorem.
Shared phase frames carry genuine current environment/local data, avoiding
repeated assumptions about later padding or allocator outcomes.

Validation: current-keccak-complete-frame-call-v1.log PASS1046jobs/permitted
printed axioms, including current full header cost/return/caller. Index8349
modules/16859facts; inventory8392/replacement closure0/frozen main unchanged.
Incremental policy65170entries/2483874589bytes PASS.
No global finite target K/full verification; claim infinity. Next: derive
actual startup workspace geometry, real current validate_headers allocation/
loop/caller costs, later current paths and uniform target-step composition.
Usage9%weekly/0resetcredits;8GiBguard/twoslots/cachefalse.

## Actual software permutation/block write frames and globals

The actual permutation writes only its25state words. The scalar width of each
actual store follows from the same checked local declarations/assignments;
a reusable scalar-local invariant includes loops, timeouts and lexical exits.
Actual ABI inversion establishes those local types inside the real caller.
Both aligned/unaligned absorb loops derive the real eight-byte index and protect
every word outside the state region; the subsequent real software permutation
call retains that frame. No cryptographic output/oracle relation is assumed.

The full actual keccak256, block absorber and permutation preserve every global
on every outcome. This includes the real heap and workspace pointer bindings.
A thin generic word-operation result lemma derives scalar stored values from
the successful expression read. Actual immutable evaluator fields remain exact.

Validation: current-keccak-absorb-frame-call-v4.log PASS758jobs/permitted printed
axioms. Index8342modules/16845facts; inventory8385/replacement closure0/frozen
main unchanged. Incremental policy65163entries/2483837480bytes PASS.
No global finite target K/full verification; claim infinity.
Next: whole-hash memory frame through actual block/padding/output phases,
real current startup workspace geometry and actual header validation loop;
later current paths and uniform target-step composition remain open.

## Complete actual software Keccak source-clock bound

The actual Software keccak_f1600 index90 permutation costs≤24source ticks
on all outcomes, from its literal24-round loop. No accelerated FFI body is
substituted. Actual absorb_block91 costs≤42body/43caller ticks (17lanes plus
that permutation), and whole keccak25692 costs≤44*(bytes/136)+689body ticks,
plus1ordinary caller. Only the real byte-count local, byte-count+136<2^64
and installed actual code are premises. Normal block exit derives the actual
remainder<136 before padding; failed pointer reads/mapping/stores are priced.
Straight-line target instruction work remains a separate open obligation.

Cleanup shares a small leading-declaration cost lemma; actual syntax and ABI
are separated from old Keccak oracle proof imports. Three old generic loop
helpers now use core classical/Nat facts instead of relying on accidental
transitive Mathlib imports; statements/semantics unchanged.

Validation: current-keccak-complete-cost-v7.log PASS730jobs/permitted printed
axioms. Index8335modules/16830facts; inventory8378/replacement closure0/frozen
main unchanged. Incremental policy65156entries/2483801516bytes PASS.
No global finite target K/full verification; claim infinity.
Next: actual Keccak write frame and current validate_headers loop, then later
current paths and uniform target-step composition. Usage8%weekly/0resetcredits.

## Current header return, memory frame and caller trace

The complete unchanged decode_header208 now derives its actual returned
248-byte record, real allocation room/alignment, initialized arenas and exact
next heap from genuine normal execution. It preserves all memory below its
entering heap, every other global, the memory domain and byte order. Successful
heap growth is at most616bytes (368slice records+248header).

The literal field pipeline carries both fallthrough and returned frames,
including lexical restoration and actual assigned helper values. Its caller
trace covers every stopped outcome or supplies that genuine fresh header,
forward clock, paid cost and original continuation. No later successful decode,
physical record, scratch mapping or allocation funding is assumed.

Validation: current-header-complete-frame-call-v1.log PASS962jobs/permitted
printed axioms. Index8325modules/16801facts; inventory8368/replacement closure0/
frozen main unchanged. Incremental policy65145entries/2483766552bytes PASS.
No global finite target K/full verification; infinity
claim unchanged. Next: current Keccak software permutation/block/fullhash and
the actual header-validation loop; later current paths/target composition open.

## Complete current header decoder body/caller source bound

Whole unchanged Software decode_header208 body/caller cost≤195*length+473/+474
source ticks on every outcome. Real complete RLP parsing, kind/count rejection,
slice counting/allocation/records, actual248-byte allocation and full typed
field pipeline are composed. Only initial current arenas, real bounded aligned
heap cursor and input-before-heap geometry are premises. Every later parser
value, record model, count and allocation room is derived from its same actual
normal return. No future success or mapped scratch is assumed.

The actual canonical count/allocation entry now establishes the complete
physical field-state invariant. Its fresh output allocation protects prior
input/records through every field. Count-check traces are generalized to arbitrary
exception metadata; the literal rejected branch spends no source ticks even
when its exception metadata is invalid. Historical narrower wrappers remain.
Arithmetic normalization is separated from the large source syntax to avoid
unnecessary evaluator unfolding during elaboration.

Validation: current-header-complete-cost-entry-v6.log PASS957jobs/permitted
printed axioms, including earlier actual normal field-entry return. Index8319
modules/16792facts; inventory8362/replacement closure0/frozen main unchanged.
Incremental policy65139entries/2483727940bytes PASS.
No global finite target K/full verification; claim infinity. Next: normal header
return/value/earlier-memory frame and actual header-validation/Keccak loop;
later current paths and global target-step composition remain open.
8GiBguard/twoslots/cachefalse; account7%weekly/0resetcredits/ordinary usage allowed.

## Complete literal current header field-pipeline source bound

The unchanged decode_header208 afterAllocation pipeline now costs≤92*payloadBytes
+455 source ticks on every outcome, given its reached physical field-entry
state. Each real encoded row is decoded at most twice; all five helper bodies,
actual callers, checked local shapes, guard choices, stores and restorations
are included. Normal fragments retain input/records, initialized arenas, real
output allocation/heap and active local types. The whole header parser/allocator
to field-state connection and complete header body cost remain open.

The common helper interface prices every stopped outcome and supplies each
real typed return, full nonlocal frame, actual child clock and true continuation.
Actual assigned calls retain the same physical state and derive their new value.
Header stores obtain their real flattened word count from reached slot shapes;
the bounded genuine writes preserve all input bytes and record cells.

Cleanup isolates shared helper/slot/store/pipeline syntax, static obligations,
step identities and four-word shape facts from old mapped-arena costs and
serializer code. Historical compatibility modules/imports remain available;
scalar carrier facts are shared instead of duplicated. No executable changes.

Validation: current-header-field-pipeline-main-v3.log PASS2030jobs, including
main/root/header entry, all current helpers, field-state/store/scope frames,
static price aggregation and complete literal field pipeline; permitted printed
axioms. Index8313modules/16783facts; inventory8356/replacement closure0/frozen
main unchanged. Incremental policy65133entries/2483706121bytes PASS.
No global finite target K/full verification; claim infinity. Next: derive the
field-entry state from actual complete parsing/count/allocation, whole header
all-outcome cost and later callers/target-step composition.
8GiBguard/twoslots/cachefalse; account7%weekly/0resetcredits/ordinary usage allowed.

## Current four-word byte conversion and complete u256 header field

The literal Software u256_from_be80 body costs≤max(4,length) source ticks on
every outcome with its real byte-count local. Its slow byte loop uses the
actual counter; its fast branch makes four actual bswap64 calls. Literal
bswap6418 is quiet/readonly and installed entries check. Both whole conversion
branches preserve every nonlocal field, including stopped and timeout paths.

Actual hdr_u256_field205 uses the real unsigned field slice and its own32-byte
guard. Its body costs≤46*selectedItemLength+45 source ticks on every outcome;
normal returns retain all nonlocal state. All five actual header field kinds
now have current source body costs and complete normal nonlocal frames.
Whole field-pipeline/header composition remains open; these are not target K.

Cleanup isolates four-word carrier/ABI facts from serializer implementation
while keeping its historical public namespace/import compatibility. The carrier
read theorem is FFI-polymorphic. A duplicate CounterFlow.declared theorem was
removed from its compatibility module; the existing shared proof supplies the
same interface. Actual conversion syntax no longer imports the large arithmetic
catalogue. No executable program or fixed semantics/proofs were changed.

Validation: current-header-u256-frame-main-v1.log PASS2005jobs, including main/
root/header connection, field entry, word/u256 fields and conversion frames;
permitted printed axioms. Index8296modules/16764facts; inventory8336/replacement
closure0/frozen main unchanged. Incremental policy65111entries/2483655630bytes PASS.
No global finite target K/full verification; claim infinity. Next: current
five-kind helper interface, protected field-pipeline state/cost and complete
header paths, then later source paths and target-step composition.
8GiBguard/twoslots/cachefalse; account6%weekly/0resetcredits/ordinary usage allowed.

## Actual field values/record reads and current word-field body/frame

Normal uint/bytes/raw fields now derive their actual contained string slice
and precise scalar/pair return value from the real item parser and kind check.
The literal width/maximum checks and physical selected-row arguments check
without importing historical mapped-arena costs. Actual hdr_word_field204
uses the real uint result; its literal guard caps the byte loop at8ticks.
Whole word-field body costs≤46*selectedItemLength+20 source ticks on every
outcome. Normal returns retain all nonlocal state. No future field result,
byte mapping, allocation room or loop run is assumed.

Cleanup splits pure record-index lookup from old scratch-footprint transport,
field value/check syntax from historical frame costs, the field ABI from
old cost imports, and the word-loop bound from its mapped-arena caller.
The generic snapshot-counter proof now uses core classical contradiction,
removing its accidental dependence on a transitive tactic import. Public
compatibility modules retain historical definitions and conditional theorems.

Validation: current-header-word-frame-v1.log PASS912jobs/permitted printed
axioms. Index8288modules/16746facts; inventory8328/replacement closure0/frozen
main unchanged. Incremental policy65102entries/2483628887bytes PASS.
No global finite target K/full verification; claim infinity. Next: current
u256 field/conversion, field state/pipeline, complete header and later paths.
8GiBguard/twoslots/cachefalse; account6%weekly/0resetcredits/ordinary usage allowed.

## Current header field entry, three field bodies and full normal frames

Real current header returns now reach the unchanged field pipeline only after
the genuine21/23 count dispatch and248-byte allocation. Actual room at the
current2952790016 heap limit is derived from that same successful allocation;
no future allocation is assumed. Field-entry memory retains the real parsed
records and its consumed prefix costs≤103*length+18 source ticks. Count and
allocation trace proofs include all stopped alternatives locally; whole header
all-outcome cost composition remains open.

Actual uint/bytes/raw field helper bodies and installed entries203/206/207
check against current Software. Each costs≤46*selectedRowLength+11 source
ticks on every outcome under actual initialized arenas and row extent. Every
normal body retains the entire nonlocal state. Literal guard tails are shared,
quiet and readonly. A reusable real item-caller interface derives its actual
contained result and canonical caller state before pricing continuations.

Cleanup separates literal count/field syntax and pure tail effects from old
mapped-arena costs; existing compatibility imports are retained. Count bindings
and normal dispatch now replay with minimal current imports. No program change.

Validation: current-header-field-frame-v2.log PASS900jobs/permitted printed
axioms. Index8280modules/16743facts; inventory8320/replacement closure0/frozen
main unchanged. Incremental policy65094entries/2483616967bytes PASS.
No global finite target K/full verification. Next: real field return values,
word/u256 fields, current field-pipeline state/cost and complete header paths.
8GiBguard/twoslots/cachefalse; account5%weekly/0resetcredits/ordinary usage allowed.

## Actual validated items, physical slice records and header list prefix

Real list-count returns now derive an ordered encoding sequence covering the
entire input and its exact count, with a complete nonlocal frame. Current
list-to-slices returns derive the same sequence, exact stored pointer/length
records, allocator room at2952790016, actual heap update and preserved arenas.
Memory outside the fresh array is unchanged; input provenance survives both
actual passes. The real scoped caller retains all these facts, its real clock,
later continuation and lexical restoration. No mapped scratch/cutoff is needed.

The literal current decode_header at index208 now has a thin shared syntax
module. Its real normal prefix derives a complete top-level list, passes the
kind check, and reaches the genuine slice records before field extraction.
This consumed prefix costs≤103*length+17 source ticks. Whole decode_header and
all stopped-prefix/header field paths still need composition; this is not K.

Cleanup removes scalar assignment's serializer import (Solver closure124→8),
uses the shared scalar carrier fact in reader observations, gives byte-reader
and slice-restoration proofs their direct binding imports, and isolates the
pure input-byte window theorem from historical arena updates. Existing legacy
compatibility interfaces remain; no runtime program/semantics is changed.

Validation: current-rlp-records-main-replay-v1.log PASS1966jobs and
current-header-list-prefix-v2.log PASS884jobs/permitted printed axioms.
Index8270modules/16734facts; inventory8310/replacement closure0/frozen main
unchanged. Incremental policy65084entries/2483589862bytes PASS.
No global finite target K/full verification; claim infinity. Next: actual
21/23 header count/allocation, field pipeline and later current callers.
8GiBguard/twoslots/cachefalse; account5%weekly/0resetcredits/ordinary usage allowed.

## Actual item/full decoder and list-to-slices source bounds

Current item body costs≤46*length+10, complete decoder≤46*length+12
and ordinary complete-decoder caller≤46*length+13 source ticks. All outcomes
are included under actual initialized arenas and a nonwrapping input extent.
Normal item returns derive their real four-word value, positive contained
total, binary kind and complete nonlocal frame. Full decode derives exact
input consumption; its real scoped caller preserves the same value/state,
real child clock, actual later continuation and lexical restoration.

Current list-to-slices body costs≤57*length+3, including actual count,
allocation, bounded unchecked second pass and both record stores. It assumes
no future successful allocation or array. Its normal array/record model is
still open for current main. Unchecked parser syntax now checks actual Software.
Shared item/full-decode/slices syntax and item value facts are separated from
historical mapped-arena clients, whose compatibility imports remain available.

Validation: current-rlp-item-decode-slices-v1.log PASS819jobs/permitted printed
axioms. Index8257modules/16722facts; inventory8297/replacement closure0/frozen
main unchanged. Incremental policy65070entries/2483545733bytes PASS.
No global finite target K/full verification; claim infinity. Next: actual
header prefix and normal slice records, field/header bounds and later callers.
8GiBguard/twoslots/cachefalse; account5%weekly/0resetcredits/ordinary usage allowed.

## Shared actual arena contract separated from initialization implementation

The same four-field ArenaState contract now lives in its own minimal module.
The actual main startup trace still establishes it; consumers no longer import
all initialization implementations to use its cursor/domain/code facts.
ArenaFrame Solver closure97→10, current list-count caller245→175 and current
public validator caller229→159. Public names and all four fields are preserved;
no program, memory layout, execution, hypothesis or bound changes.

Validation: current-arena-interface-main-list-cleanup-v1.log PASS1910jobs,
including actual main decoder/root/verification/header connection and the whole
current list-count caller; permitted printed axioms only. Index8241modules/
16688facts; inventory8281 includes one pending item-syntax extraction. Replacement
closure0/frozen main unchanged. No global finite target K/full verification;
claim infinity. Next: current item/slice/header bounds and actual later callers.
8GiBguard/twoslots/cachefalse; account4%weekly/0resetcredits/ordinary usage allowed.

## Complete actual list-count source body/caller and normal input frame

Whole current rlp_list_count body/caller cost≤46*length/+1 source ticks,
including the actual counter/offset declarations, each real parsed item,
two increments and final return, on all outcomes. Each continuing iteration
pays from its actual consumed bytes, so one input byte budget covers the loop.
Actual positive item size derives both increments without word wrap.

Real normal returns derive a word count≤original length and preserve every
nonlocal field. Actual ignored and scoped callers keep that same count and
pure caller state. Continuation pricing uses only the real count return;
no future allocation room or successful parser is supplied. Literal current
syntax and pure assignment proofs are shared with historical clients, whose
mapped-arena contracts remain unclaimed for current main.

Validation: current-rlp-list-count-caller-v1.log PASS864jobs/permitted printed
axioms. Index8240modules/16688facts; inventory8279/replacement closure0/frozen
main unchanged. Incremental policy65051entries/2483475170bytes PASS.
No global finite target K/full verification; claim infinity.
Next: simplify the shared arena interface imports, then current item/slice/header
costs and normal frames, later actual paths and global target-step composition.
8GiBguard/twoslots/cachefalse; account4%weekly/0resetcredits/ordinary usage allowed.

## Current item-total source bound and actual consumed-byte caller budget

Complete current rlp_item_total costs≤14*inputLength+30 source ticks on all
outcomes under actual initialized arenas and a nonwrapping input extent.
A normal result derives its actual positive consumed-byte word≤inputLength,
complete nonlocal frame and cost≤14*consumedBytes+30. The real scoped caller
supplies that same byte advance, exact resumed caller, lexical restoration
and cost≤14*consumedBytes+31. Flat byte-string continuations cost zero source
ticks. List iterations can now share their actual input byte budget.

Cleanup separates ItemTotalProgram's actual current syntax/ABI/argument facts
from legacy mapped-arena costs, preserving the public syntax names. The old
conditional cost module remains historical and unclaimed for current main.
The current proofs use the checked public validator and actual header result;
no mapped scratch, future successful parser or allocator room is supplied.

Validation: current-rlp-item-total-caller-budget-v2.log PASS854jobs/permitted
printed axioms. Index8231modules/16670facts; inventory8270/replacement closure0/
frozen main unchanged. Incremental policy65041entries/2483444662bytes PASS.
No global finite target K/full verification; claim infinity.
Next: current list-count shared byte-budget proof, then complete item/slice/header
and actual later source paths. 8GiBguard/twoslots/cachefalse; account4%weekly,
0resetcredits, ordinary usage allowed.

## Complete actual public RLP validator cost and normal memory/arena frame

The public unchanged rlp_validate_items body/caller now cost≤14*(length+1)+4
/+5 source ticks, including actual saved mark, caught RLP-error release/raise,
normal release/return and every stopped outcome. The internal and public bodies
return zero and preserve all nonlocal state on real normal returns. The actual
ignored public caller supplies that same complete memory/global/arena/heap frame.
No later successful parser or extra allocation room is assumed.

Continuing step proofs retain their exact nonlocal frame. Generic loop-invariant
composition carries it through actual normal exits and all four local scopes.
The real handler cannot fall through or return, so caught normal calls derive
the same internal body return. Release reinstalls the actual unchanged entering
cursor. Scratch mark/release syntax uses current Software; shared caught-call
inversion works for any FFI state, removing an accidental Guest import.

Validation: current-rlp-public-body-caller-frame-v1.log PASS848jobs/permitted
printed axioms. Index8227modules/16662facts; inventory8266/replacement closure0/
frozen main unchanged. Incremental policy65037entries/2483427465bytes PASS.
No global finite target K/full verification; claim infinity.
Next: isolate shared current item/list syntax from old mapped-arena contracts,
then current item/list/header bounds and normal frames, actual later paths and
target compilation/global literal K. Resource guard8GiB/twoslots/cachefalse;
account3%weekly,0resetcredits, ordinary usage allowed.

## Complete actual internal RLP validator source body/caller bound

The unchanged _rlp_validate_items_body now costs≤14*(length+1) source ticks;
its real uncaught caller adds one. All outcomes, exhausted clocks, actual
setup declarations, parser/allocator failures and final return are included.
Entry uses the real initialized scratch2701127680/frame2688618496 and ordinary
domain plus a nonwrapping input extent. No mapped scratch, allocation room,
future successful parse or assumed input bytes are supplied.

A continuing body either advances its real position within a fixed end or
finishes the list. Its actual nested push cannot continue: the checked allocator
return is a word, the literal raw-rec first store is below ordinary memory,
and the caller's existing after-word is retained. A physical natural rank
prices the loop, reusing the checked byte parser and13-tick body allowance.
The old hypothetical mapped-arena validator remains conditional and unused.
Shared ArenaState.of_frame transports real arena facts through pure scopes.

Validation: current-rlp-actual-body-caller-main-check-v1.log PASS1883jobs,
including current main/root/header connection after shared-helper cleanup;
permitted printed axioms only. Index8223modules/16652facts; inventory8262,
replacement closure0/frozen main unchanged. Incremental policy65033entries/
2483403489bytes PASS. 8GiBguard/twoslots/cachefalse,
disk61%, account3%weekly/0resetcredits/ordinary usage allowed. No global finite
target K/full verification; claim infinity.
Next: internal normal memory/arena frame, real caught release wrapper and
whole header/source paths, then target-step compilation/global literal K.

## Current RLP byte parser, validator step and real variable scratch store

The actual current rlp_item_header body/caller cost≤10/11 source ticks;
normal return derives its actual binary flag and positive nonwrapping item
extent inside the current input. One actual internal validator loop body
costs≤13. A real scratch allocation followed by storing an existing scalar
caller word cannot continue below ordinary memory; its actual allocator return
supplies the address, without extra room or a future successful helper premise.

Rlp.Fail drops the obsolete full gas/EVM import umbrella. HeaderCost Solver
closure251→56; ReadLengthCall243→48. Current Software AST names are used for
selected parser/validator syntax and entries. The scalar carrier fact no longer
imports unrelated serializer/U256 implementation. Needed bindings/code/address
facts are imported directly; Nat transitivity uses the core theorem. Shared
scoped_none now works for arbitrary FFI state, removing an accidental Guest
import requirement. Public parser interfaces are retained.

The old Rlp.Validation.Arena.lower requires frame memory≥2701131776, which
cannot follow from the actual initialized2688618496. Do not apply that old
whole-validator theorem to current main. Next prove flat continuing parses
and failed nested scratch pushes under the real arena, then close the whole
validator/current header caller. Current Keccak and subsequent databases also
remain open. No global finite target K/full verification; claim infinity.

Validation: current-rlp-validator-step-variable-store-v8.log PASS752jobs,
permitted printed axioms only. Index8215modules/16637facts; inventory8254,
replacement closure0/frozen main unchanged. Incremental policy65024entries/
2483372784bytes PASS. 8GiBguard/twoslots/cachefalse; account2%weekly,
0resetcredits, ordinary usage allowed. Failed diagnostics remain unindexed.

## Actual verification wrappers and header caller from the same main run

The current verify/attempt chain reaches the actual current run_attempt with
all three physical witness arrays, six SI fields, real scratch/frame arenas,
entering heap and bounded physical payload gas cell. MainRootTrace keeps each
stopped alternative and the real serialization/output continuation. HeaderReached
retains the actual first payload declaration/skip, header caller/run, argument
loads and lexical restoration; no future validator success is assumed.

Cleanup separates the actual Software run_attempt body/current entry803 from
obsolete header contracts. All seven wrapper bodies/entries and verify entry811
now use current Software. Direct binding imports replace transitive accidental
ones. AttemptWrapperChain Solver closure1601→54; VerifyProgram1603→56. These
are proof import counts, not runtime improvements. No program bytes change.

Validation: current-main-verification-header-joined-v1.log PASS1828jobs,
permitted printed axioms only. 8GiBguard/twoslots/cachefalse. Index8213modules/
16634facts; inventory8252/replacement closure0/frozen main unchanged. Incremental
policy65022entries/2483366118bytes PASS. Account
2%weekly,0resetcredits; ordinary usage allowed. No global finite target K/full
verification; claim infinity. Actual current header/RLP bounds and crypto/map
joins remain open, alongside target compilation and complete source paths.
Next: remove obsolete RLP import umbrella, check the current header/RLP costs.

## Actual main root return retains all three witness arrays

The same decoder now supplies all six physical SI witness pointer/count fields,
complete node/code/header records, validated item lengths1024/65536/1024 and
headercount≤256 after main's actual normal root call. The original decoder
heap is identified with its actual root allocation, bounding the three earlier
array extents. The final witness result retains the already-proved node/code
ordering instead of discarding it. One shared WitnessArrays.Image and interval
frame transports all three arrays; one argument-load proof handles both SI
loads, including empty arrays. RootReturned retains the actual initialized
scratch/frame arenas, workspace and entering persistent frontier.

Validation: current-main-root-witness-images-v1.log PASS1807jobs and
current-witness-array-arguments-v3.log PASS1464jobs, permitted printed axioms
only. Index8205modules/16622facts; inventory8244, replacement closure0 and
frozen main unchanged. Incremental policy65013entries/2483341403bytes PASS.
Account2%weekly,0resetcredits, ordinary usage allowed.
Source source-cost/normal-frame proofs remain distinct from target-step and
covered-outcome work. No global finite target K/full verification; claim infinity.
Next: minimal current verification wrappers, actual header caller and scratch path.

## Complete actual current root body and main caller cost/memory

The unchanged htr_new_payload_request now has a complete source allowance:
its four established child caller prices plus413 for the body, plus one for
the actual main caller. This includes the real saved mark/128-byte allocation,
payload/header-list/header-copy/request calls, final Merkle and release. Both
child contracts come from the same decoder/root allocation; each actual normal
prefix derives the next complete physical SI/RQ/payload image and real heap.
Observed non-timeout stopped prefixes, including allocation failure, are priced.
Normal whole body and main caller protect earlier metadata outside the actual
output/length chunk and restore the entering heap. No future successful hash
or extra temporary room premise is supplied.

Shared InvocationFrame handles direct local frames and actual protected-memory
intervals; root geometry derives input/header bounds and SI separation from the
same decoder. Optional cosmetic arithmetic expansion was removed after its
elaboration hit the memory guard; the real composition theorems check quickly.
No source/compiler/frozen bytes change. Source clocks still omit straight-line
target work; covered-terminal classification and global target steps remain open.

Validation: current-root-main-cost-frame-v5.log PASS1802jobs, permitted printed
axioms only. 8GiBguard/twoslots/cachefalse. Index8199modules/16615facts;
inventory8238/replacement closure0/frozen main unchanged. Incremental policy
65007entries/2483319736bytes PASS. Account1%weekly,0resetcredits, ordinary
usage allowed. No global finite target K/full verification; claim infinity.
Next: actual main-to-stateless-verification arena/metadata and scratch boundary.

## Complete current payload protected-memory and restored-heap caller frame

The whole unchanged payload body and its real two-word caller now preserve
any earlier protected word outside the actual output/length chunk and restore
the entering heap on the same normal return. The query may be outside the
payload record, covering earlier SI/RQ metadata at the actual root caller.
The proof includes literal static fields/extra data, both actual root allocations,
transaction and withdrawal loops/lists, saved releases, balance and container.
Normal prefix inversions select the same real continuation; nested allocations
derive their own room and mapped extents. No future successful helper or extra
temporary allocation room is supplied as a premise.

PayloadWithdrawalSuffix/Allocation/ScopeMemory and matching transaction modules
compose the established component frames. PayloadPrefixMemory, PayloadMemory
and PayloadCallMemory close the actual enclosing scopes and ABI. Actual decoder,
workspace, frontier and separation facts remain root call-entry obligations.
Source-cost and normal memory/heap results are separate; neither classifies
terminal errors as covered or prices compiled target straight-line work.

Validation: current-payload-whole-caller-memory-v1.log PASS1489jobs/permitted
printed axioms only. 8GiBguard/twoslots/cachefalse, disk61%. Index8183modules/
16574facts; inventory8222, replacement closure0, frozen main unchanged.
Incremental policy64991entries/2483258806bytes PASS. Latest account reading
0%weekly,0resetcredits; ordinary usage allowed. No reset was invoked by this
agent. No global finite target K or full verification; claim infinity.
Next: actual root allocation/call-entry data and complete root hash joins.

## Complete actual current htr_payload body and two-word caller source bound

Whole payload body allowance is5*actual total transaction bytes+3391*actual
transaction count+848*actual withdrawal count+5*actual balance bytes+16695;
the real two-word caller adds one. This joins the literal initial raw load,
outer mark/608-byte chunk allocation, static fields, extra list, transaction
snapshot/root allocation/loop/list/release, actual ordinary assigned withdrawal
roots allocation, withdrawal loop/list/release, balance, nineteen-field container
and final release. Each same real normal prefix supplies its next complete
decoded image, caller locals and heap; earlier failed allocations and all
observed non-timeout stops remain included. Entry obligations still need to be
derived at the actual root caller. No successful future hash or extra temporary
allocation room is assumed. This is source call/loop work, not target steps.

Shared state/cursor/list transport keeps the same decoded payload through both
dynamic phases. Saved cursor geometry comes from the real earlier mark. Generic
assigned-call facts now work for any FFI state, removing a stale hidden Guest
import. Pure local-frame transport uses the existing direct decoded frame
instead of rebuilding interval ownership. Explicit scalar declaration states
keep the final checks small; failed/guard-stopped diagnostic logs were not
indexed. Complete generic payload protected-memory composition and root joins
remain open, alongside target straight-line and global covered-path work.

Validation: current-payload-whole-caller-v1.log PASS1475jobs/permitted printed
axioms only, covering all19newmodules and selected dependencies. 8GiBguard/
twoslots/cachefalse, disk61%. Index8174modules/16554facts; inventory8213,
replacement closure0, frozen main unchanged. Incremental policy64982entries/
2483211493bytes PASS. Account33%weekly,0resetcredits; ordinary usage allowed.
No global finite target K or full verification; claim infinity.

## Same-decoder payload state, real byte regions and complete final phase

PayloadDecodedBudget derives the raw540-byte arena, actual withdrawal count
and44-byte extent, and real balance pointer/length/arena from the same decoder's
validated offsets and copied input. It assumes no sixteen-withdrawal schema
maximum. PayloadState and shared actual-call transport retain the complete
physical decoded image through current static field prefixes, extra data and
balance hashing. Literal source expressions and original function bytes stay
unchanged. Static memory/cost pipelines share current FixedRecord proofs.

Extra data has actual caller source cost≤270. The complete final phase has
source cost≤5*balanceBytes+8325, including its three scalar fields, balance hash,
actual nineteen-field container and saved-mark release. Its protected-memory
frame also checks, including the actual n=19 activity-mask bound. The actual
parent dynamic allocations and transaction/withdrawal phase joins remain open.

Validation: current-payload-extra-final-memory-v4.log PASS1450jobs/permitted
printed axioms only, covering all eight new modules and selected dependencies.
8GiBguard/twoslots/cachefalse. Index8155modules/16505facts; inventory8194,
replacement closure0, frozen main unchanged. Incremental policy64963entries/
2483120226bytes PASS. Account32%weekly,0resetcredits; ordinary usage allowed.
No global finite target K or full verification; claim infinity.

## Actual current transaction/withdrawal loops and minimal shared arithmetic

The current transaction loop has all observed non-timeout source cost at most
5*sum(actual transaction lengths)+3303*actual count. Each real continuing hash
preserves every physical decoded row and the initialized workspace and restores
the entering heap; actual increments supply the next bounded index. The complete
normal loop also preserves arbitrary earlier metadata outside actual roots and
length workspace. TransactionEntry derives the row image, each actual item arena,
count/length bounds and shared byte budget from the same normal decoder records
and real parent root-array geometry. Whole payload allocation/phase joins remain.

The literal withdrawal loop costs760ticks per actual record, including its call
and loop tick and all observed non-timeout failures. Its complete normal memory
frame checks against the actual44-byte records and32-byte root slots.

Cleanup moves unchanged public prefix-sum and array/pointer facts into minimal
modules, preserving their names. Geometry no longer needs the old Keccak wrapper;
new current cost arithmetic no longer imports the whole decoder record proof.
current-varlist-shared-import-cleanup.json records the static Solver closures.
The unselected historical ConstructorData wrapper remains unclaimed/current
crypto migration work; its hash-buffer proof body was not changed.

Validation: current-payload-withdrawal-cost-v1.log PASS1152jobs,
current-payload-transaction-round-v1.log PASS1285jobs,
current-payload-transaction-step-v1.log PASS1286jobs,
current-payload-transaction-cost-v2.log PASS1377jobs,
current-payload-transaction-memory-v1.log PASS1379jobs,
current-payload-withdrawal-memory-v1.log PASS1287jobs,
current-payload-transaction-entry-v1.log PASS1391jobs. Permitted printed axioms
only;8GiBguard/twoslots/cachefalse, disk61%. Index8147modules/16471facts;
inventory8186, replacement closure0, frozen main unchanged. Incremental policy
64955entries/2483070781bytes PASS. Account32%weekly,0resetcredits; ordinary usage
allowed. No global finite target K or full verification; claim infinity.

## Current payload syntax, shared fixed-field costs and complete heap restoration

PayloadProgram/Scopes match the actual current htr_payload, including the
ordinary assigned withdrawal roots allocation and both m2 releases. Shared
FixedRecord field prices apply to the literal current payload calls via checked
source argument/program equivalence: first1668, middle84, last162. Literal
raw+0 stays in the current AST and still needs its actual target work counted.
PayloadHeap proves normal whole-body heap restoration without counts, mapped
inputs, intermediate heap values or additional allocation room as premises.
Transaction/withdrawal cost and metadata joins remain open.

Validation: current-payload-static-step-v1.log PASS1151jobs and
current-payload-heap-v1.log PASS1158jobs; permitted printed axioms only.
8GiBguard/twoslots/cachefalse. Index8138modules/16441facts; inventory8177,
replacement closure0, frozen main unchanged. Incremental policy64946entries/
2483015611bytes PASS. Account32%weekly,0resetcredits; ordinary usage allowed.
No global finite target K or full verification; claim infinity.

## Complete actual parent requests protected-memory and heap caller frame checks

RequestsMemoryPipeline retains any earlier protected word through the same real
five list calls and final five-field container/release. Each continuing call
also supplies the next actual decoded image using RequestsState.after_list.
RequestsMemory joins the actual parent allocation, outer mark and both lexical
restorations. The whole current parent body and real two-word caller preserve
metadata outside their actual output/length chunk and restore entering heap.
Real decoded image, initialized workspace, frontier/separation and protected
query facts remain explicit call-entry obligations. No future helper success
or additional temporary room is assumed.

Validation: current-parent-requests-memory-v1.log PASS1401jobs/permitted printed
axioms only;8GiBguard/twoslots/cachefalse, disk61%. Index8133modules/16418facts;
inventory8172, replacement closure0, frozen main unchanged. Incremental policy
64941entries/2482989783bytes PASS. Account31%weekly,0resetcredits; ordinary usage
allowed. No global finite target K or full verification; claim infinity.
Next: current payload static fields/transaction and withdrawal loops, complete
payload/root costs and memory joins, then actual main/scratch covered paths.

## Complete actual htr_requests body and caller source cost checks

RequestsState derives each real list call's protected RQ-field frame, restored
heap, current workspace/code/domain facts and next complete decoded image.
RequestsPipelineCost composes those same actual normal prefixes, all five
selected list costs and the five-field container/release tail. Failed helper
paths stop inside their own bound; later field reads are never assumed.

RequestsAllocation derives the actual160-byte chunk arena, room and next heap
from AllocationScopeCost's same real return/nonlocal frame. RequestsCost joins
that allocation and actual outer mark/restoration. Complete current htr_requests
body/caller source cost is≤13*(requestSize-20)+19488/19489 on the same actual
non-timeout outcome. Entry obligations remain the real decoded image, installed
code/domain, initialized workspaces and actual frontier. No future successful
hash, additional allocator room or output/input data contents are assumed.
This is a source call/loop bound, not a formal target-step bound.

Validation: current-parent-requests-cost-v2.log PASS1396jobs/permitted printed
axioms only;8GiBguard/twoslots/cachefalse, disk61%. Index8131modules/16410facts;
inventory8170, replacement closure0, frozen main unchanged. Incremental policy
64939entries/2482976892bytes PASS. Account31%weekly,0resetcredits; ordinary usage
allowed. No global finite target K or full verification; claim infinity.
Next: parent request protected memory/caller frame, payload and root composition.

## Actual parent request syntax/arguments and shared price budget check

RequestsProgram matches the whole current htr_requests source: five literal
list calls, five-field container and saved mark/release. Its actual normal
body restores the entering heap with no count/mapping/room premises.
RequestsEntry uses the complete decoded RQ image and real mapping to derive
all five actual pointer/count/size/output argument lists and physical record
extents. RequestsBudget proves their checked caller allowances sum to at most
13*(requestSize-20)+15870 source ticks, using the single encoded byte budget.
This is arithmetic on the established allowances; whole parent cost composition
and metadata preservation between these calls still remain open.

AllocationScopeCost prices every same non-timeout scoped allocator outcome.
Only its same checked normal return supplies actual returned cursor, persistent
room and complete nonlocal post-state to the real continuation. Failed
allocations are charged without assuming future success. This supports joining
parent metadata/ownership to later call-entry obligations.

Validation: current-parent-requests-entry-v1.log PASS1273jobs,
current-parent-requests-budget-v1.log PASS1246jobs and
current-allocation-scope-cost-v1.log PASS283jobs; permitted printed axioms only.
8GiBguard/twoslots/cachefalse, disk61%. Index8127modules/16397facts; inventory8166,
replacement closure0, frozen main unchanged. Incremental policy64935entries/
2482954487bytes PASS. Account31%weekly,0resetcredits; ordinary usage allowed.
No global finite target K or full verification; claim infinity. Next: actual
parent request call memory/image transport and whole request/payload/root costs.

## Same-decoder complete request image and shared byte budget reach root callee

RequestsReturned now retains its already proved first/valid offset facts.
DecodedRequestsImage derives the full ten physical RQ fields, actual slice and
count arithmetic from that same returned decoder; proves request/SI store
separation; and transports the image through the real witness prefix to the
exact main snapshot. Invocation.Data now carries it through the actual root
allocation and into the same actual root hasher callee. Persistent allocation
ordering derives encodedLength≤251655056, input lower/arena, aligned80-byte RQ
and its position after copied input. No decoder validity/counts are assumed.

Requests.ImageLayout shares the existing Image/Layout definitions and memory
transport. ByteBudget imports that minimal interface, reducing its static Solver
closure227→103; current-request-byte-budget-import-cleanup.json records the
comparison. DecodedBudget derives each actual list's complete physical input
extent and count≤134217728, plus the shared exact five-list byte budget and
sum(counts)≤(requestSize-20)/68. Whole parent hash composition still remains.

Validation: current-request-image-at-root-v2.log PASS1519jobs and
current-decoded-request-budget-v3.log PASS1078jobs; permitted printed axioms only,
8GiBguard/twoslots/cachefalse, disk61%. Index8123modules/16384facts; inventory8162,
replacement closure0, frozen main unchanged. Account30%weekly,0resetcredits;
ordinary usage allowed. Incremental policy64931entries/2482941352bytes PASS.
No global finite target K or full verification; claim infinity. An exploratory selection of historical Requests.BodyTrace also hit
unchanged obsolete KeccakOracle accelerator identifiers and a historical
Requests.Setup code-entry mismatch (current-request-image-layout-v1.log FAIL).
Those modules remain historical/unclaimed; only the successful current/minimal
closures above are indexed. The shared-definition extraction preserves their
public definition names; their old proofs were not otherwise edited.

## Complete actual selected request-list memory and heap caller frame checks

RequestListMemoryStep joins actual input record/output slot arenas to the
selected fixed-record call and transports the real heap/context. The five
literal dispatch branches and final increment compose without assuming future
record success. RequestListMemoryLoop retains the actual decoded kind/p/n/size,
protected metadata/current heap and derived next indices through every normal
iteration. Its workspace-global certificate covers the actual loop.

RequestListMemory joins the real root-array allocation (including its extra32
bytes), actual i scope, loop, final progressive list/release and saved mark.
Its real five-word caller inherits both memory and entering-heap frames.
Persistent room comes from this same allocation; actual count, complete physical
record extent, output/workspaces/current-heap facts remain parent obligations.
bound.md now consolidates the completed helper work and states the remaining
whole payload/request-root and actual decoder-image joins directly.

Validation: current-request-list-memory-v1.log PASS1295jobs/permitted printed
axioms only;8GiBguard/twoslots/cachefalse, disk61%. Index8119modules/16371facts;
inventory8158, replacement closure0, frozen main unchanged. Incremental policy
64927entries/2482925552bytes PASS. Account30%weekly,0resetcredits; ordinary usage
allowed. No global finite target K or full verification; claim infinity.
Next: same-decoder full request/payload images at parent hash entries and joins.

## Complete actual container memory and heap caller frame checks

Current PContainerBitMemory checks the real activity byte store and bounded
normal loop for n≤256, fitting its32-byte mask. PContainerMemorySuffix joins
actual act/i scopes, clear, bit loop, software SHA output and release. Only the
actual output expression is located for SHA; digest/input mapping is not a
memory premise. PContainerMemory joins the same actual64-byte allocation,
progressive call, complete marked body and real three-word caller. Metadata
survives and entering heap is restored; persistent room comes from its actual
allocation. The physical input extent and field count remain explicit parent
obligations. Actual current parents use19 and5 fields; their joins remain open.
The wider all-outcome source-cost theorem is unchanged.

Validation: current-container-memory-v1.log PASS1274jobs/permitted printed axioms
only;8GiBguard/twoslots/cachefalse, disk61%. Index8116modules/16358facts;
inventory8155, replacement closure0, frozen main unchanged. Account30%weekly,
0resetcredits; ordinary usage allowed. Incremental policy64924entries/
2482901273bytes PASS. No global finite target K or full verification; claim
infinity. Next: request-list and complete payload/root joins.

## Actual progressive list/byte wrappers and shared output caller frame check

WordTripleLookup and MemoryOutputCall share checked last-output binding and
same normal caller inversion while the first two argument values/expressions
remain unrestricted. Current software SHA reuses them without changing its
public theorem interfaces. MixMemory gains the corresponding output-only frame.

PListMemory joins actual progressive hashing and length mixing, retaining
metadata and entering heap with arbitrary length word. PBytesMemory joins the
same scoped pack return/tuple/count, progressive list call and final release;
its actual three-word caller inherits both memory and heap frames. Physical
input/output/zero-table/length-chunk/current-heap facts remain parent obligations;
no temporary-room or future callee success is assumed.

Validation: current-shared-output-and-list-v2.log PASS1290jobs (also rechecks
fixed-record/progressive/byte dependencies); current-progressive-byte-memory-v1.log
PASS1283jobs, permitted printed axioms only.8GiBguard/twoslots/cachefalse, disk61%.
Index8113modules/16348facts; inventory8152, replacement closure0, frozen main
unchanged. Incremental policy64921entries/2482878976bytes PASS. Account29%weekly,
0resetcredits; ordinary usage allowed. No global finite target K or full
verification; claim infinity. Next: container and
request-list memory/resource joins, then complete payload/request-root.

## Complete actual progressive hash memory and heap caller frame checks

ProgressiveMemoryStep joins each actual capped Merkle call, current input/root
slot extents and counter updates. ProgressiveMemoryLoop preserves the same
protected metadata/current heap through every geometric round and derives its
actual terminal round. ProgressiveMemoryFold checks decrement-before-SHA and
complete clear/fold/output/release; only accumulator output is located, with
no digest or SHA-input mapping assumptions.

MemoryContextAllocation shares real normal allocation inversion and derives
persistent room, physical arena and next bounded/aligned heap context for its
same continuation. ProgressiveMemory joins the actual768/32-byte allocations,
three initializing declarations, whole loop/fold/output scopes and real caller.
Earlier metadata survives and the entering heap is restored. Count/physical
input/output/zero-table/current-heap facts remain explicit parent obligations;
no reserved temporary room or future successful helper is assumed.

Validation: current-progressive-memory-v1.log PASS1267jobs/permitted printed
axioms only;8GiBguard/twoslots/cachefalse, disk61%. Index8109modules/16336facts;
inventory8148, replacement closure0, frozen main unchanged. Incremental policy
64917entries/2482856750bytes PASS. Account29%weekly,0resetcredits; ordinary usage
allowed. No global finite target K or full verification; claim infinity.
Next: progressive list/byte/container and complete payload/request joins.

## All six complete actual fixed-record memory and heap caller frames check

FixedRecordMemorySteps shares actual u64/copy/vector call frames and sequential
field composition. Record lengths and real allocated chunk extents derive each
field's input/output arena and alignment. FixedRecordMemory joins those fields
to the final actual Merkle/release, initial mark and real two-word callers. The
same normal allocation derives persistent room and next aligned heap; no old
accelerator or reserved temporary-room premise is retained. Earlier metadata
and entering heap survive every genuine normal record return.

Cleanup moves pipeline_prefix into FixedRecordPipeline so runtime and memory
proofs share it. MemoryContextTransport reuses the checked current helper graph
to transport workspace/code/domain facts alongside each actual heap frame.

Validation: current-fixed-record-memory-v2.log PASS1282jobs, including existing
FixedRecordCost after the cleanup; permitted printed axioms only.8GiBguard/
twoslots/cachefalse, disk61%. Index8104modules/16318facts; inventory8143,
replacement closure0, frozen main unchanged. Account29%weekly,0resetcredits;
ordinary usage allowed. Incremental policy64912entries/2482821531bytes PASS.
No global finite target K or full verification; claim infinity. Next: actual
progressive loop/fold/whole-body memory joins.

## Complete actual byte list/vector memory and heap caller frames check

PackBytesScopeMemory inverts the same actual scoped pack call, derives its real
buffer tuple, persistent room, next heap bounds/alignment and protected word,
and passes them into its actual continuation with lexical restoration intact.
Both byte-vector branches and the whole byte-list body now retain metadata and
restore their entering heap. BytesCallMemory joins their actual three/four-word
ABIs to these same callee proofs. Temporary allocation room and successful
future helpers are not caller premises; physical input/output/workspace and
count/depth facts remain explicit parent/root obligations.

Validation: current-byte-call-memory-v2.log PASS1257jobs/permitted printed axioms
only;8GiBguard/twoslots/cachefalse, disk61%. Index8099modules/16306facts;
inventory8138, replacement closure0, frozen main unchanged. Account29%weekly,
0resetcredits; ordinary usage allowed. Incremental policy64907entries/
2482797966bytes PASS. No global finite target K or full verification; claim
infinity. Next: fixed-record/progressive/payload composition.

## Actual byte heap restoration and length-mix memory frame check

Both actual byte-vector branches and the byte-list body restore exactly their
entering heap on a genuine normal return. SavedHeapReturn now handles release
followed by a checked heap-preserving suffix; this covers the list length mix.
PureGlobals checks actual basic/st_le64/mix/u64 helper effects and real callers.

ByteOutputFrame recognizes a bare output pointer as offset zero and proves its
actual expression read. WordPairLookup identifies the known pointer even when
the other argument has unrestricted shape. WordStoreMemory checks actual32/64bit
stores; MixMemory joins the real zero/store/software-SHA calls and preserves
metadata outside the32-byte length chunk and output. No digest/input mapping or
future callee success is assumed. Complete byte memory composition remains open.

Validation: current-word-store-memory-v2.log PASS1228jobs (also rechecks complete
MerkleMemory); current-mix-memory-v1.log PASS1187jobs, permitted printed axioms
only;8GiBguard/twoslots/cachefalse. Index8095modules/16295facts; inventory8134,
replacement closure0, frozen main unchanged; incremental policy64903entries/
2482765844bytes PASS. Account29%weekly,0resetcredits; ordinary usage allowed.
No global finite target K or full verification; claim infinity.

## Complete actual Merkle memory and heap caller frame checks

MerkleAllocationMemory derives persistent cursor+32*capacity room from the same
real allocation return, then establishes the aligned temporary arena and exact
caller locals for copy/clear/dense/extension/output. The actual size declaration
and heap_mark scope preserve the protected metadata word; final normal return
restores the entering heap. No future successful allocation or room is assumed.

MerkleMemory joins the real logarithm/max prefix, including its actual minimal
count/limit depths and lexical restoration. The empty-tree branch copies the
real zero-table slot without modifying heap. The complete body and its actual
four-word caller retain both protected memory and entering heap. Real source
n/limit bounds, input/output arenas, ordinary domain, zero table and persistent
cursor facts are explicit entry obligations; their eventual parent/root joins
remain necessary. Source code and all error-path cost bounds remain unchanged.

Validation: current-merkle-complete-frame-v1.log PASS1226jobs/permitted printed
axioms only;8GiBguard/twoslots/cachefalse, disk61%. Index8090modules/16266facts;
inventory8129, replacement closure0, frozen main unchanged; incremental policy
64898entries/2482734199bytes PASS. No global finite target K or full verification;
claim infinity. Next: whole byte/progressive/fixed-record memory composition and
real payload/request-root ownership/resource joins.

## Shared actual saved-mark restoration checks on current hash bodies

SavedHeapReturn inverts the real normal heap_release assignment, deriving its
own validity/shape facts with no assumed previous heap cell. Its structural
Tail proof tracks the actual saved caller binding through foreign lexical
bindings, arbitrary scoped callees and no-return prefixes. The real heap_mark
call supplies that saved value in the same normal parent run; final release
therefore restores exactly the entering heap.

MarkedHeap instantiates the grammar against actual current source syntax for
the nonempty Merkle phase, all six fixed-record hashes, progressive hashing,
progressive bytes/container and the complete request-list body. These normal
heap-restoration theorems assume no counts, mapped input/output, workspace,
intermediate heap value, allocation room or future successful callees. This
shares heap reasoning without replacing any current Pancake code. Allocation/
depth memory joins and empty-Merkle/full-byte-list heap cases remain open.

Validation: current-marked-hash-heap-v1.log PASS1180jobs/permitted printed axioms
only;8GiBguard/twoslots/cachefalse, disk61%. Index8088modules/16256facts; inventory
8127, replacement closure0, frozen main unchanged; incremental policy64896entries/
2482711872bytes PASS. Account28%weekly,0resetcredits; ordinary usage allowed.
No global finite target K or full verification; claim infinity.

## Complete current Merkle buffer/dense/extension/output memory frame checks

The actual outer body derives half=cur/2 and its j=0 inner entry. Every real
pair output stays in the same temporary buffer; normal iteration derives the
next half count and preserves the buffer pointer. The whole normal shrinking
dense loop preserves a protected word outside that buffer, without old SHA
state/accelerator or mapped SHA-input premises. All globals, including the heap
pointer, survive the dense phase on every outcome.

MerkleSuffixMemory joins the same actual dense, extension, output copy and
release returns. MerkleBufferMemory adds the real input copy, padding clear and
cur declaration. A protected metadata word stays unchanged outside the actual
temporary buffer and final32-byte output. Physical copy/zero arenas and current
counter/depth inputs are explicit; actual buffer allocation room and depth-prefix
joins, and whole helper heap restoration, still need closing.

Cleanup gives HeapScopeCost the real Software mark/release entries and minimal
imports. Solver closures: heap scope225→22, copy-return252→114, heap-return227→27;
static comparison is current-heap-import-cleanup.json. ScopedCallNormal imports
its actual HostMemory type directly. Existing normal release/copy-return/heap
frames recheck without pulling obsolete table/EVM proofs into this closure.

Validation: current-merkle-buffer-memory-v2.log PASS1162jobs/permitted printed
axioms only, including HeapReleaseReturn and ScopedCallNormal.8GiBguard/twoslots/
cachefalse; disk61%. Index8086modules/16237facts; inventory8125, replacement
closure0, fixed main unchanged; incremental policy64894entries/2482692432bytes
PASS. No global finite target K or full verification; claim infinity.

## Actual packing image and Merkle pair-loop memory frames check

PackBytesMemory.Returned retains the exact returned(buffer,ceil(n/32)) tuple,
persistent request room≤2952790016, actual next heap, monotonicity/alignment/
upper bound, and a protected word below the real incoming cursor. The same
actual normal allocator call derives room; a geometric ordinary-domain extent
is never substituted for allocation room. The length premise n+64<2^64 includes
current251655056-byte inputs. Its buffer/caller frames use actual copy and
short padding returns. Shared PackBytesArguments supplies the identical amount/
padding arithmetic to runtime and memory proofs.

LoopBodyEffects structurally certifies call-free local-assignment loops preserve
every global, on all outcomes. MemoryGlobals checks that actual Software copy/
zero syntax and their real callers satisfy it. This includes the heap pointer.
SHA's checked caller frame now only needs its actual output expression located;
input expressions/contents/mapping remain unrestricted. Actual Merkle dense and
extension pair steps/loops preserve protected words using their real counter
and32-byte output slot, including the correct decrement/increment placement.
No obsolete SHA state/accelerator buffers or successful future calls are used.

Validation: current-pack-frame-complete-v1.log PASS1222jobs, including complete
current request-list/PBytes/container callers and scalar/SHA frames;
current-merkle-pair-memory-v2.log PASS733jobs. Permitted printed axioms only;
8GiBguard/twoslots/cachefalse, disk61%. Index8083modules/16223facts; inventory8122,
replacement closure0, fixed main files unchanged; incremental policy64891entries/
2482668495bytes PASS. Account27%weekly,0resetcredits. No global finite target K,
no full verification; claim infinity. Next: complete dense/fill/extension/root
memory and heap restoration, then the actual payload/request-root composition.

## Current memory primitives and scalar-root output frame check

U64Memory checks actual scalar-root zero32/copy8/return syntax and its two-word
caller. On the same genuine normal return it preserves every word outside the
32-byte output. Physical input8/output32 arenas and output alignment are entry
facts, while both helper continuations and caller locals come from that run.
The current copy, aligned-zero and unaligned short-zero memory frames also
recheck; no future successful callee outcome is supplied.

Cleanup replaces ZeroCost's broad original-code umbrella with the real Software
entry and minimal interfaces, drops an unused copy cost/short-zero cost import,
and makes missing direct dependencies explicit. Solver import closures shrink:
copy/zero246→96, short-zero266→119, ZeroCost231→49. Static comparison is in
current-memory-import-cleanup.json. Shared three-word ABI removes the duplicate
SHA caller environment proof. MemoryBoundedLoop uses its explicit current
comparison case instead of relying on a transitively imported tactic.

Validation: current-hash-memory-primitives-v4.log PASS765jobs/permitted printed
axioms only;8GiBguard/twoslots/cachefalse. Index8078modules/16204facts; inventory
8117, replacement closure0 and fixed main files unchanged. Incremental policy
64886entries/2482638885bytes PASS. No global finite target K or full verification;
claim infinity. Next: actual packing return derives persistent allocation room
and metadata frame, then complete current SSZ hash ownership composition.

## Complete current request-list dispatch, loop, body and caller check

The actual five tests charge exactly one selected fixed-record hash. The
selected kind and fixed record size come from this same five-word call, and
ordinary caller-local restoration retains the real count/pointers through the
iteration. A potential(selectedRecordPrice+2)*(n-index) pays each loop tick and
that selected hash, including actual failed prefixes. Normal iterations derive
the increment and retained input bindings; normal exits preserve the current
counter state without supplying any future result.

The complete actual body composes both real allocation scopes, index0,
dispatch/loop, progressive list/mix and release. For actual n≤134217728:
body≤(selectedRecordPrice+90)*n+3173, real caller adds1. Allocation failures,
read/store errors and traps remain included in the same non-timeout outcome.
No mapped input/output, accelerator workspace, heap room or successful hash
premises are needed for these costs. Physical record/RQ lifetimes and the full
payload/request-root join remain open.

Validation: current-request-list-caller-v1.log PASS1171jobs/permitted printed
axioms only;8GiBguard/twoslots/cachefalse. Index8077modules/16198facts; inventory
8116, replacement closure0, fixed main files unchanged. Incremental policy
64885entries/2482631547bytes PASS; no full verification. Claim infinity and no
global finite target K. Account26%weekly,0resetcredits; ordinary usage allowed.

## Current container and six fixed-record hash costs check

The actual activity-bit loop uses the shared signed-counter theorem:≤n-index
source ticks for nonnegative n<2^63, including failed byte reads/stores. The
clear/bit-loop/software-SHA/release suffix costs≤n+44. Complete actual
progressive-container body/caller≤89*n+3168/3169 for n≤134217728 on the same
observed non-timeout execution. Real mark/64-byte allocation failures are
included; no future success, mapped pointer, workspace or heap room is assumed.

Current fixed-record proofs compose each real scalar/vector/copy field and its
actual Merkle/release suffix. Same observed non-timeout body prices check:
withdrawal758, deposit1425, wdreq880, cons1144, bdep1279, bexit734; actual
ordinary callers add1. Their pointer and returned temporary bindings come from
the same execution. No old accelerator or geometry assumptions are needed for
these costs. Physical metadata lifetimes and target straight-line work remain
separate open obligations.

Cleanup adds byte stores to the shared LocalPrefix structural theorem and
removes ByteStoreLocal's duplicate proof. Current container syntax/bit-loop/
suffix Solver import closures shrink613→9/614→40/616→128; the exact static
comparison is current-container-import-cleanup.json. Historical consumers remain
unselected; their old runtime proofs are not claimed current.

Validation: current-container-record-complete-v1.log PASS1634jobs/permitted
printed axioms only, including current Invocation, PBytes, byte callers and SHA
output memory frame.8GiBguard/twoslots/cachefalse; disk61%. Proof index8070modules/
16171facts; Solver inventory8109, replacement closure0, frozen main files
unchanged. Incremental policy64878entries/2482592679bytes PASS. No global finite
target K, no full verification; claim infinity. Next: actual request-list
selection/loops and complete physical payload/request-root composition.

## Progressive list/byte wrappers and shared ABI cleanup

Current PListCost checks the complete real progressive/mix/return body and its
four-word caller:≤88*n+3168/3169 for n≤134217728. PBytesCost composes mark,
packing, that exact returned pointer/count, progressive list and release:
body/caller≤packPrice(n)+88*ceil(n/32)+3172/3173. The byte length must satisfy
n+64<2^64 and actual packed count≤134217728. All same observed non-timeout
outcomes, including allocation failures and traps, are covered without
successful hashing, memory mapping, workspace or future funding assumptions.

Cleanup reuses the existing arbitrary-name three-word ABI theorem for the
common p/n/out signature. Its generic API is retained for existing consumers;
current progressive and byte wrappers share this specialization.

Validation: current-progressive-wrapper-complete-v1.log PASS1627jobs, permitted
printed axioms only;8GiBguard/twoslots/cachefalse. Proof index8063modules/
16142facts. Account26%weekly,0resetcredits, ordinary usage allowed. No global
finite target K or full verification; claim infinity. Next: current container
wrapper, fixed record hashes and complete actual payload/request-root joins.

## Complete current progressive hashing body and caller now check

The actual geometric step uses its real capped count, Merkle limit4^k, pointer
expressions and three counter updates. Continuing executions derive precisely
the next round, without heap/mapping/workspace premises. Actual n≤134217728
implies at most15rounds. A potential88*(n-off)+200*(15-k) pays each round and its
actual consumed chunks; the normal loop supplies the terminal fold count.

The current fold spends≤2ticks/root on every outcome. Its clear/fold/output/release
suffix costs≤2*k+85. Actual constant declarations establish round0; all three
real mark/roots/acc allocation scopes include failed and partial paths. Complete
current progressive body/caller cost≤88*n+3120/3121 for the same observed
non-timeout execution. No successful hash, allocator room, mapped arena, obsolete
accelerator state or future funding is assumed. Target straight-line work and
whole request/payload composition remain open.

Cleanup separates current syntax, pure cap/update/counter facts and ABI from the
historical accelerator-dependent frames. Old wrappers retain their names/imports
for historical consumers; their old runtime proofs are not claimed current.
Solver import closures: pure geometric budget562→1, current program568→35,
updates570→37, fold program569→62 (old comparison restores six changed sources
to previous HEAD). ObserveDeclaration shares actual arbitrary-outcome scalar
scope inversion and lexical restoration.

Validation: current-progressive-complete-cost-v1.log PASS1623jobs/permitted printed
axioms;8GiBguard/twoslots/cachefalse. Index8061modules/16131facts; account25%weekly/
0resetcredits. No global finite target K; claim infinity; no full verification.
Next: progressive list/byte/container wrappers, physical memory frames and complete
actual payload/request-root hashing.

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

## Current main supplies the whole header context — 2026-10-28

The actual first three initializer calls derive the current software Keccak
state2701132160 and pad2701132360. Extended the shared startup/root global
frames to carry both cells alongside the existing SSZ workspace; no replacement
implementation or old accelerated Keccak environment is used. Real decoded
witness images establish all validator rows, lengths and entry geometry at
main's actual caller. A genuine scoped header return preserves SI/payload/gas
and all three witness images, with the actual advanced heap and Keccak context.

Validation: current-main-header-context-returned-v1.log PASS2125jobs, permitted
printed axioms only. Index8383modules/16928facts; inventory8427modules,
replacement AST reverse closure0, fixed files unchanged. Incremental policy
PASS65206entries/2484008072bytes; no full verifier claim. Generators syntax
checked without regenerating cleaned imports. Claim infinity, no global K.
Next: the actual post-header gas/database/state path, then whole current source
and target-step composition. Overall estimate remains40%, plausible30–50%.
Five old unfinished RLP files preserved untracked. Account10%weekly used,
zero reset credits, ordinary usage allowed.

## Actual header/gas prefix reaches the current Patricia database — 2026-10-28

The actual run_attempt either stops within51528390source ticks or reaches
the first nodedb_build call with full current SI/payload/gas/Keccak/witness
input data. This retains all outcomes and actual lexical action/continuation
frames. The current gas check includes gas-used/gas-limit guards and the
software udiv/udivmod call chain (≤66body ticks, complete prefix≤67). Its
constant1024divisor derives a full nonlocal frame, including short-clock
timeouts. Neither a successful check nor a future helper outcome is assumed.

The current decoded node image supplies its true two-word ABI and strict
count<2^31 from actual record extent/current heap ceiling. Reused only the
literally unchanged capacity loop:≤30ticks, sufficient power2^bits,
2≤bits≤32, capacity≤4*count+4, full state frame and actual allocation tail.
The current Patricia htab_new has four allocations/no clearing loop and
costs≤8body ticks on all outcomes. Its insertion/tree proof remains open.
Cleanup removed the redundant intermediate gas-only prefix module before
committing; generic current-call frame/constant-operand adapters are shared.

Validation: current-patricia-new-main-entry-capacity-v1.log PASS2143jobs,
permitted printed axioms only. Index8397modules/16958facts, inventory8441modules,
replacement AST reverse closure0, fixed files unchanged. Incremental policy
PASS65221entries/2484059426bytes; no full verifier claim, claim infinity, no
global target K. Next: real Patricia initialization/insertions, remaining
current main/source paths and target-step composition. Overall estimate40%,
plausible30–50%. Five old unfinished RLP files preserved untracked.
Account11%weekly used, zero reset credits, ordinary usage allowed.

## Current Patricia constructor: complete cost/return/layout — 2026-10-28

Actual htab_new now has a reached-entry bound≤5source body ticks for32-byte
keys, an actual bounded/aligned current heap and capacity≥2. This includes
all four allocation calls, allocation traps/timeouts, minimum-capacity/stride
declarations and all11metadata stores. Each request's room is derived at that
same actual call. A normal return derives4paid ticks, the real table pointer,
all four request-room facts and the exact canonical nonlocal state.

The constructor writes exactly11fields: keylen32,stride32,capacity,emptycount0,
keys/nodes/order pointers,emptyroot0,nextnode1,free0,nodecapacity. The same
returned state protects every word before the fresh table. Actual physical
layout is88metadata bytes plus two32*(capacity+1)arrays and one8*(capacity+1)
array; the reserved zero slots and all real rounded allocation frontiers are
retained. Sourceheap≥2701131776/end≤2952790016 imply capacity≤3495251; when
the real capacity loop's power/sufficiency facts are supplied this yields
bits≤21 and builder count≤1048575. Array/field proof is actual Software code,
not the former hash-map layout. Insertion/tree invariants remain open.

Cleanup: shared one actual array-allocation/pointer-store proof across all
three arrays. Strengthened the common scoped-call/allocator trace to classify
stopped outcomes as unable to return from the enclosing function, retaining
the former numeric API as a compatibility projection. This prevents a cheap
stopped alternative from replacing a real returned constructor state.

Validation: current-patricia-constructor-geometry-main-v7.log PASS2160jobs,
permitted printed axioms only; all modified helper/main dependencies replayed.
Index8412modules/16988facts; inventory8456modules, replacement AST reverse
closure0, fixed files unchanged. Incremental policy PASS65236entries/
2484122431bytes; no full verifier claim. Claim infinity, no global target K.
Next: current constructor normal caller/workspace frame into node-builder
loop; actual Patricia find/insert tree invariants, remaining current main
paths and target-step composition. Overall estimate40%, plausible30–50%.
Five old unfinished RLP files preserved untracked. Account12%weekly used,
zero reset credits, ordinary usage allowed.

## Current main enters the real initialized Patricia builder — 2026-10-28

Connected the full current constructor return/layout to its actual scoped
caller and database capacity loop. The database body stops within36source
ticks or reaches the original insertion-loop continuation with the genuine
empty Patricia header/arrays, current arena/Keccak workspace, advanced
persistent frontier and protected earlier input. Actual returned capacities
force bits≤21 and count≤1048575. The first caller in current run_attempt now
selects this same child execution from its real decoded node image/ABI.
Its later codedb/main continuation is retained explicitly on all outcomes.

Cleanup: one physical workspace interface and an explicit source-frame
re-anchoring lemma carry the same returned table across actual callee/caller
locals and clock, without identifying the entire two states. The normal
caller is a projection of the classified all-outcome interface. No future
constructor success or independently selected returned state is assumed.

Validation: current-main-patricia-builder-reached-v4.log PASS2165jobs,
permitted printed axioms only. Index8417modules/17001facts, inventory8461,
replacement AST reverse closure0, fixed files unchanged. Incremental policy
PASS65241entries/2484147331bytes; no full verification claimed, claim infinity,
no global target K. Next: actual Patricia find/insert invariant and raw
witness/Keccak scratch separation, complete builder/current main paths and
uniform target composition. Account12%weekly used; zero reset credits.
Five old unfinished RLP files preserved untracked. Overall estimate40%,
plausible30–50%; module counts remain bookkeeping.

## Actual current find-leaf traversal and shared-helper cleanup — 2026-10-28

Current Software htab_find_leaf119 body≤257source ticks/caller≤258 from
a reached mapped32-byte-key table with an increasing-bit node image. The
actual loop uses rank257−nodeBit; every normal internal step chooses a real
left/right child with a larger bit, and marker256 breaks. Failed key-byte
reads, wrong operands, short clocks and every other outcome are retained.
Actual normal branch/source bindings, scoped b restoration and full
nonlocal read-only effects are checked. Physical empty tables return0 in
0body ticks at every clock, without any node/key contents premise.

This is a local traversal contract. The actual insertion history still
has to establish/preserve the node image before a whole database bound can
use it. No global target K or new finite certificate is claimed.

Cleanup extracted the generic mapped scalar load from the witness-decoder
pipeline into Input.LoadWord, retaining its existing namespace and making
it host-polymorphic. Both copy/memzero cost files now share the generic
actual normally-continuing conditional lemma instead of duplicate case
analyses. Existing APIs are preserved, current main/root dependencies replayed.

Validation: current-patricia-find-leaf-caller-empty-v7.log PASS2175jobs,
permitted printed axioms only. Index8427modules/17025facts; inventory8471,
replacement AST reverse closure0, fixed files unchanged. Incremental policy
PASS65252entries/2484184597bytes; no full verification. Claim infinity.
Next: actual traversal normal leaf result, first-difference semantics and
Patricia insertion invariant, raw witness/Keccak scratch separation, remaining
current main paths and uniform target composition. Overall estimate40%,
plausible30–50%. Five old unfinished RLP files preserved untracked.
Account12%weekly used, zero reset credits, ordinary usage allowed.


## Actual normal Patricia lookup caller and genuine empty base — 2026-10-28

The actual find-leaf loop exits with zero or a real mapped leaf at bit256.
Its scoped caller carries that same result, full physical memory/global
frame and exact continuation, including all earlier stopped outcomes. A
genuine htab_new return supplies the vacuous empty node image and real table
header/alignment, without assuming initialized node contents or future calls.
Insertion history still has to establish/preserve the image after updates.

Cleanup added shared actual break/continue-aware normal loop exit and
NoReturn conditional helpers; constructor workspace now retains the actual
table alignment through source-frame re-anchoring.

Validation: current-patricia-find-normal-caller-empty-base-v4.log PASS2181jobs,
permitted printed axioms only. Index8433modules/17039facts, inventory8477,
replacement AST reverse closure0, fixed files unchanged. Incremental policy
PASS65258entries/2484208525bytes; no full verification or global target K,
claim infinity. Next: actual first-difference semantics and insertion image,
workspace separation, remaining main paths and uniform target composition.
Overall estimate40%, plausible30–50%. Five old unfinished RLP files preserved
untracked. Account13%weekly used, zero reset credits, ordinary usage allowed.


## Current first-difference costs and real byte-scan progress — 2026-10-28

Actual htab_first_diff118 body costs≤9*keyLength and its scoped caller
≤9*keyLength+1, giving288/289source ticks for actual32-byte keys. These
all-outcome bounds include failed reads, early returns and short clocks; no
key contents, byte mappings or future successful scan is a pricing premise.
Actual full nonlocal read-only effects and caller frame check as well.

A genuinely continuing bit step skipped a zero digit and advanced its actual
j counter. Falling through the full signed0..8bit loop forces its byte xor
to zero; the actual outer step therefore continues only on a zero byte xor.
Current key mathematics uses most-significant-first bits, including complete
key separation, least mismatch uniqueness/marker and preceding byte agreement.
The full source return-to-least-mismatch and insertion image are still open.

Cleanup extends shared LocalFlow to actual loops with early returns and
factors one counter rank proof over a preserved optional local snapshot.
Existing no-return counter APIs remain compatibility projections; captured
expression loops now reuse that rank proof instead of duplicating it. Shared
fallthrough counter preservation also handles early-return prefixes. Actual
current main/root and existing lookup callers replay after these changes.

Validation: current-first-diff-bit-cost-v7.log PASS1882jobs, permitted printed
axioms only. Index8440modules/17064facts; inventory8484, replacement AST reverse
closure0 and fixed files unchanged. Incremental policy PASS65266entries/
2484243110bytes; no full verification or global target K, claim infinity.
Next: source least-difference semantics and actual insertion image, workspace
separation, remaining main paths and uniform target composition. Overall
estimate40%, plausible30–50%. Five old unfinished RLP files preserved untracked.
Account14%weekly used, zero reset credits, ordinary usage allowed.


## Actual full first-difference return and caller — 2026-10-28

The unchanged htab_first_diff118 now returns the actual least mismatch in
current most-significant-first order, or marker256 for equal32-byte keys.
The proof reads genuine physical key bytes from the same execution, carries
the zero digit/byte prefixes, handles early returns and full normal loop
completion, and retains the complete physical frame. Its classified scoped
caller either stops within289source ticks or reaches the exact original
continuation with that same returned word; a cheap stopped alternative cannot
stand in for an enclosing normal return. Previous288body/289caller costs remain.

Cleanup shares actual inner/outer read-only effects and one bit-prefix
progress proof between normal and early-return loop outcomes. Current key
byte views remain independent of historical bit-order conventions. No source
program changes and no assumed future completed first-difference scan.
Actual insertion still has to establish/preserve tree order and physical
array/key ownership; a whole database/global target bound is not claimed.

Validation: current-first-diff-complete-caller-v1.log PASS1889jobs, permitted
printed axioms only. Index8447modules/17081facts; inventory8491, replacement
AST reverse closure0, fixed files unchanged. Incremental policy PASS65273
entries/2484278265bytes; no full verification, claim infinity, no global K.
Next: current node allocation/leaf/internal construction and insertion image,
workspace separation, remaining main paths and uniform target composition.
Overall estimate40%, plausible30–50%. Five old unfinished RLP files preserved
untracked. Account14%weekly used, zero reset credits, ordinary usage allowed.


## Actual node allocation, available slots and key-bit observations — 2026-10-28

The current htab_new_node122 empty-free-list/no-growth path executes at any
body clock, including0, returning the genuine next index and changing only
its increment at table+64. Its classified scoped caller costs≤1source tick
or supplies that same result/single-word physical frame and original
continuation. The real table constructor now retains its actual capacity≥2,
so its returned metadata derives the first allocator context directly.
Availability after later insertions remains an obligation.

One shared slot geometry maps all real available32-byte key/node and8-byte
order slots, including reserved zero slots, without initialized-content
premises. The actual find-leaf branch mask/test now observes physical query
bytes in current most-significant-first order; shifts/modulo/aligned slot
calculations are checked against actual word expressions. These facts are
local ingredients, not a preserved insertion image or global database bound.

Validation: current-patricia-allocator-slots-key-read-v3.log PASS2199jobs,
permitted printed axioms only, including constructor/main/header/root/lookup
and first-difference callers. Index8453modules/17100facts; inventory8497,
replacement AST reverse closure0, fixed files unchanged. Incremental policy
PASS65280entries/2484309843bytes; no full verification, claim infinity and no
global target K. Next: actual branch/path semantics, leaf/internal writes and
insertion invariant; workspace separation, later main paths and target-step
composition. Overall estimate40%, plausible30–50%. Five old unfinished RLP
files preserved untracked. Account15%weekly used, zero reset credits, ordinary
usage allowed.


## Actual query-directed lookup route and insertion ordering facts — 2026-10-28

The actual internal traversal step chooses the zero/one child from real
physical query bytes and restores its temporary bit local exactly. Normal
lookup execution now derives its finite query-directed route to the actual
returned leaf; the classified scoped caller retains that same earlier route,
full physical frame and258tick allowance for its original continuation.
No independent successful lookup, guessed leaf or future terminal state is
supplied. Current htab_set126's real entry and second-search syntax check.

The logical routing model carries common prefixes and left/right split
digits along increasing-bit edges. Its route lemmas show that insertion
cannot stop at a bit equal to the earlier real first mismatch: the reached
leaf would instead agree with the query at that traversed split. This is
used to justify strict ordering when a new internal node is linked. The
actual constructor/insertion history still must establish and preserve this
logical model and its physical key images; no global database result claimed.

Validation: current-patricia-routes-set-syntax-v1.log PASS2198jobs, permitted
printed axioms only, with current main/root/database and first-difference
callers. Index8458modules/17113facts; inventory8502, replacement AST reverse
closure0, fixed files unchanged. Incremental policy PASS65286entries/
2484340197bytes; no full verification, claim infinity, no global target K.
Next: real second-search cursor/exit and insertion writes/image, workspace
separation, remaining main paths and target composition. Overall estimate40%,
plausible30–50%. Five old unfinished RLP files preserved untracked. Account15%
weekly used, zero reset credits, ordinary usage allowed.


## Actual insertion second search, cost and strict exit — 2026-10-28

The unchanged htab_set126 second-search step now executes with its actual
d/p/key locals. At b≥d it breaks; otherwise it records the real parent and
selects the same physical query-directed child as the earlier lookup. Exact
binding restoration, current header/node reads and short-clock loop outcomes
are included. The whole search costs≤257source ticks. A real normal exit
retains the actual parent edge, earlier lookup suffix route, node image and
b≥d; the genuine earlier first mismatch makes this b>d. This supplies the
strict split ordering needed for the subsequent new node links.

Cleanup shares one physical n/nodes cursor between lookup and insertion.
The functions retain their own real locals/guards; insertion is not required
to have the other function's keybits binding. Actual setup into this search,
leaf/internal writes and preserved insertion image remain to connect.

Validation: current-patricia-shared-cursor-search-bound-v1.log PASS2206jobs,
permitted printed axioms only, with existing lookup/first-difference/allocator
callers, constructor/database/current main and root. Index8461modules/17121
facts; inventory8505, replacement AST reverse closure0, fixed files unchanged.
Incremental policy PASS65289entries/2484362643bytes; no full verification,
claim infinity, no global target K. Next: actual insertion search entry and
new leaf/internal writes, preserved tree/key image; workspace separation,
later main paths and target composition. Overall estimate40%, plausible30–50%.
Five old unfinished RLP files preserved untracked. Account15%weekly used,
zero reset credits, ordinary usage allowed.


## Actual post-difference phase reaches the original insertion call — 2026-10-28

The real htab_set nodes/p/n declarations and mapped header reads initialize
the same checked second search, retaining its actual d/query locals. The
post-difference phase either stops within257source ticks or reaches the
unchanged new-leaf caller with the real strict split, parent edge, suffix
route and physical cursor. All three enclosing lexical restorations remain
explicit. An actual stopped search cannot return from htab_set, so it cannot
substitute for an enclosing normal return. No successful future node/leaf
allocation is supplied. The earlier lookup/comparison/difference phase and
subsequent insertion writes still have to join this interface.

Validation: current-patricia-reached-insertion-allocation-v1.log PASS2208jobs,
permitted printed axioms only, with actual lookup/first-difference/allocator
callers and current main/root/database. Index8464modules/17125facts;
inventory8508, replacement AST reverse closure0, fixed files unchanged.
Incremental policy PASS65292entries/2484374528bytes; no full verification,
claim infinity, no global target K. Next: real byte comparison/earlier caller
join, leaf/internal writes and preserved insertion image, workspace separation,
later main paths and target composition. Overall estimate40%, plausible30–50%.
Five old unfinished RLP files preserved untracked. Account16%weekly used, zero
reset credits, ordinary usage allowed.


## Constructor-derived table image and actual set first lookup — 2026-10-28

The shared current insertion-only table image carries the actual11header
fields, array geometry, fresh-index range, root/count/node bounds, routed
node image, real leaf-byte views and caller-specific leaf-value membership.
The genuine constructor establishes its empty base without initialized-array
contents. Actual read-only frames retain the image. Per-call node capacity
remains an explicit availability fact to derive from the builder iteration.

Current Software memeq13 is checked against its actual unchanged ABI/body.
Physical32-byte operands give≤4body/5caller source ticks at arbitrary
alignment; a real normal return identifies byte-key equality and retains the
full physical frame. Clock padding only inverts that actual normal run.
htab_set's real first two mapped header loads and lookup call now reach the
original continuation with empty0 or a real leaf/query route, retaining the
image and exact klen/stride/leaf lexical restorations on all outcomes.

Cleanup extracts the current comparison ABI and syntactic physical frame
from general dictionary-cost imports while retaining their existing APIs.
Compare Solver import closure93→55. Existing general-comparison and current
main/header/root/database callers replay after the change.

Validation: current-patricia-set-first-lookup-v2.log PASS2208jobs, permitted
printed axioms only. Index8469modules/17134facts; inventory8513, replacement
AST reverse closure0, fixed files unchanged. Incremental policy PASS65297
entries/2484398674bytes; no full verification, claim infinity, no global K.
Actual insertion still has to preserve the image after writes. Next: complete
comparison/difference caller join and real leaf/internal updates, builder
iteration/workspace separation, later main paths and target composition.
Overall estimate40%, plausible30–50%. Five old unfinished RLP files preserved
untracked. Account16%weekly used, zero reset credits, ordinary usage allowed.


## Actual comparison/difference/search connection and existing-value write — 2026-10-28

The actual nonempty set continuation loads its genuine key-array pointer,
skips the real empty guard and compares the reached leaf's actual bytes.
Its real failed-equality continuation skips the update branch, computes the
genuine first mismatch and runs the checked second search. It stops within
546source ticks or reaches the original new-leaf call with the strict split,
parent edge, suffix route and all real t/key/value/klen/stride/leaf/keys locals.
The equal-key branch performs its actual mapped leaf-value store and returns0
at every body clock, spending no source call/loop tick. Complete image
preservation after this write and fresh-node insertion remains open.

Shared local contracts retain the actual caller bindings through helper
returns. The search now explicitly proves preservation of every local except
its n/p assignments, including restoration of temporary b, and its reached
allocation interface retains those facts. Shared image facts provide node
slot/range checks, fresh indices and two available node indices from the
actual processed-entry count and sufficient capacity, without future success.
Comparison reuses the shared slot/range proof rather than repeating it.

Validation: current-patricia-comparison-difference-update-v1.log PASS2227jobs,
permitted printed axioms only, with current lookup/first-difference/allocator
callers and main/root/database. Index8476modules/17151facts; inventory8520,
replacement AST reverse closure0, fixed files unchanged. Incremental policy
PASS65304entries/2484433745bytes; no full verification, claim infinity and no
global target K. Next: actual update/image preservation, fresh leaf/internal
writes and full insertion invariant; builder iteration/workspace separation,
later main paths and target composition. Overall estimate40%, plausible30–50%.
Five old unfinished RLP files preserved untracked. Account16%weekly used,
zero reset credits, ordinary usage allowed.

## Actual equal-key image preservation and aligned key copy

The current htab_set equal-key branch now preserves the complete physical
Patricia image after its actual value store, including leaf-value membership.
Constructor-derived nonwrapping cell geometry rules out header/key/other-node
aliasing; internal left cells cannot alias the updated leaf value cell.
The actual aligned32-byte memcpy call costs2source ticks on every outcome;
real normal execution derives its own funding, exact four-word writes and
copied query bytes. Current caller alignment/order must still be derived.

Validation: current-patricia-real-key-copy-v2.log PASS889jobs, permitted printed
axioms only. Index8479modules/17164facts, inventory8523/replacement closure0,
fixed files unchanged; incremental policy65307entries/2484455424bytes PASS.
No global finite target K/full verification. Usage17%weekly/0resetcredits.
Next: actual fresh leaf/internal writes and complete insertion preservation.

## Original fresh leaf/internal constructors and real scoped callers

Actual htab_new_leaf123 now costs≤3body/4caller source ticks, including the
real no-grow node call,32-byte key copy and six leaf/order/count stores.
Actual htab_new_internal124 costs≤1body/2caller ticks and performs its real
four stores. Normal runs derive paid clocks and exact memory writes; stopped
outcomes are included. Both classified callers retain original continuations.
The current image derives mapped slots/header fields; query alignment and
query-before-table order must still come from the real database caller.
Shared node-address/store and key-copy-frame helpers avoid repeating those
physical arguments across the two original constructors. No source changes.

Validation: current-patricia-real-node-callers-v1.log PASS920jobs, permitted
printed axioms only. Index8490modules/17186facts; inventory8534/replacement
closure0/fixed files unchanged; incremental policy65320entries/2484517567bytes
PASS. No global finite target K/full verification. Usage17%weekly/0resetcredits.
Next: preserve full physical/routing image through actual fresh insertion.

## Actual first insertion image and fresh splice model

The original empty htab_set branch now either stops within4source ticks or
returns0 with the full genuine nonempty table image after its real leaf call
and root store. Fresh leaf writes protect earlier input, nodes and other key
slots; exact fresh cells, count and next metadata check. Actual internal-node
writes also protect old nodes/keys and unrelated metadata. The pure two-node
splice preserves routing and increasing bits; its freshness, prefix/mismatch
and extended valid-index range come from the actual image and lookup/search
route. Nonempty original rewiring still must establish that physical image.
Shared byte-store/frame/projection helpers keep those arguments small; the
first-image proof checks in about2.5seconds after avoiding eager expansion of
nested store states, rather than increasing its elaboration allowance.

Validation: current-patricia-first-insertion-image-v9.log PASS907jobs, permitted
printed axioms only. Index8506modules/17223facts; inventory8550/replacement
closure0/fixed files unchanged; incremental policy65336entries/2484589681bytes
PASS. No global finite target K/full verification. Usage18%weekly/0resetcredits.
Next: actual nonempty splice writes, full set invariant and builder loop.

## Complete original current htab_set body/caller cost

The entire unchanged32-byte-key htab_set126 now costs≤815source body ticks
and≤816ordinary caller ticks, given its reached physical image, two available
indices and actual aligned earlier query bytes. Lookup, memeq, first mismatch,
second search, leaf/internal construction and every original rewiring outcome
are included. The real leaf return derives the second allocator's metadata;
no future successful allocation or source-clock funding is supplied. The
original rewiring block is straight-line/0source ticks, failed-comparison tail
≤552, nonempty post-lookup≤557, empty post-lookup≤4. The actual empty call
cannot fall through to comparison. These source clocks omit static target work.
Nonempty fresh insertion still must preserve the physical image for iteration;
query ownership, complete builder/main and uniform target K remain open.

Validation: current-patricia-entire-insertion-caller-cost-v1.log PASS946jobs,
permitted printed axioms only. Index8516modules/17236facts; inventory8560/
replacement closure0/fixed files unchanged; incremental policy65346entries/
2484626057bytes PASS. No global finite target K/full verification. Usage18%
weekly/0resetcredits. Next: actual nonempty rewiring image and builder loop.

## Original complete nonempty rewiring execution and shared state frames

The actual post-constructor htab_set splice now executes its refresh, three
parent writes, real physical query-bit child selection, left-cell/root attach
and return0 in one checked execution theorem. Both real constructors protect
earlier input/query bytes. Shared metadata records all physical fields except
memory/locals/clock and replaces nine redundant domain/code projection facts;
the complete815body/816caller insertion cost still checks with that cleanup.
Nonempty full image assembly and original caller composition remain open.
It will also require count+1≤cap from the real builder's processed-count and
capacity facts; two available node IDs alone need not imply that count room.

Validation: current-patricia-original-entire-splice-v2.log PASS954jobs, permitted
printed axioms only. Index8528modules/17257facts; inventory8572/replacement
closure0/fixed files unchanged; incremental policy65358entries/2484664085bytes
PASS. No global finite target K/full verification. Usage19%weekly/0resetcredits.
Next: physical nonempty splice image, then full insertion/builder induction.

## Complete combined fresh-insertion physical image

The exact constructor-plus-splice memory model now establishes the full
nonempty image: all11header fields, real root/count/next updates, extended
valid-index range, mapped bit/child cells, increasing routing, physical old/
new leaf keys and witness-value membership. The actual left-cell comparison
and prior parent link establish either old parent edge; root replacement
also checks. Count room comes from the current builder counter. Real scoped
caller composition must still place this image at its same returned state
before full insertion/builder induction; no whole-builder/global bound claimed.

Validation: current-patricia-complete-fresh-image-v2.log PASS970jobs, permitted
printed axioms only, alongside full insertion cost, empty caller and existing
value-update image. Index8539modules/17283facts; inventory8583/replacement
closure0/fixed files unchanged; incremental policy65369entries/2484728466bytes
PASS. Usage19%weekly/0resetcredits. Next: real fresh caller image transport,
then full insertion return and actual builder loop.

## Complete original insertion normal return and actual builder caller

The entire actual htab_set body and ignored-result caller now return a full
physical table image on every real normal return. Empty, equal-key and fresh
branches all return0; the result adds at most one leaf, preserves all physical
fields except memory/locals/clock and protects every earlier input word. The
ordinary caller also restores its full local map. Actual failed comparison,
first mismatch, strict second search, both constructors and original splice
are one execution with exact scope restoration. No future successful run or
funding is supplied. Matching815body/816caller all-outcome cost still checks.
Actual database iteration, main's MPT-query workspace ownership and remaining
source/target composition are open; no global finite target K/full verification.

Validation: current-patricia-entire-insertion-real-caller-v2.log PASS981jobs,
permitted printed axioms only. Index8550modules/17296facts; inventory8594/
replacement closure0/fixed files unchanged; incremental policy65380entries/
2484769018bytes PASS. Usage20%weekly/0resetcredits. Next: current builder loop
and actual startup MPT scratch/input separation, without assuming a stronger
copied-input frontier or reusing stale pre-rebase initializer constants.

## Actual MPT initializer/main workspace and shared frame cleanup

The current mpt_init223 normal body and ignored caller derive their actual
five allocations,184bytes of room and complete global template. The same
first-four main execution gives hash buffer2701134768 and heap frontier
2701134824. All nine later initializers retain both, including the actual
EVM saved-mark release. Main's decoder/root-allocation traces preserve that
pointer. No independent successful hash/allocation or future funding premise.

Cleanup shares42large syntax-effect proofs in one six-key core and retains
all43old five-key APIs as wrappers; mpt_init's own restricted proof stays
outside the core because it initializes the sixth key. The actual decoder
prefix supports the new key. Generator layout check passes. Need propagate
the stronger heap/input lower frontier and real MPT pointer into decoded
witness/builder contexts; the old2701134640 bound falls below this buffer.

Validation: current-workspace-shared-core-v1.log PASS272jobs;
current-workspace-extended-api-v1.log PASS1609jobs;
current-actual-mpt-workspace-return-v1.log PASS839jobs;
current-mpt-main-workspace-v1.log PASS1600jobs. Permitted printed axioms only.
Index8554modules/17343facts; inventory8599/replacement closure0/fixed files
unchanged. No global finite target K/full verification. Usage20%weekly,
0resetcredits. Next: carry derived MPT separation into actual builder loop.

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


## Complete unchanged current MPT decode step

Current _decode_step235 costs≤n/4+195*n+284body source ticks for n≤1024 at
its actual current heap/arena entry. Parsing, real allocated slice records,
compact/path/value calls, leaf constructor/stores and branch/extension cuts
are connected through their same actual executions. All normal returns have
flag zero, which will exclude recursive-frame work in the enclosing loop.
No future allocation success is assumed. Shared slice-result syntax and
key-byte span imports were cleaned up; actual persistent room is retained
separately from ordinary-domain bounds.

Validation: current-mpt-step-main-regression-v1.log PASS2590jobs, including
actual main/state_init entry and the new decode-step path/permitted printed
axioms; index8632modules/17477facts. Inventory8677/replacement closure0/
fixed files unchanged. Incremental policy PASS65467entries/2485107882bytes.
Overall estimate45%, plausible35–55%, relative to rebased main. No global
finite target K/full verification; claim infinity. Usage26%weekly/0resetcredits.
Continue actual witness loop/wrappers/state_init and later main/target work.


## Complete unchanged witness/root/state initialization source bounds

Actual witness core236 costs≤200223, MPT catch237≤200225, scratch/catch
wrapper238≤200229, whole root decoder239≤200544 and state_init320≤200624
body source ticks on all outcomes at their derived actual entries. The real
first decode's normal result forces empty-stack return mode and one final
exit iteration. Matching real lookup images supply any materialized witness;
workspace writes protect these images, and genuine allocation derives room.
The initializer suffix uses all eight actual Patricia constructors and remaining
allocations for78ticks, including20/32/52-byte keys. Shared syntax imports no
longer drag in old registry/hashmap runtime proofs. No program/claim change.

Validation: current-state-init-complete-v2.log PASS2637jobs/permitted printed
axioms; index8639modules/17491facts. Inventory8684/replacement closure0/fixed
files unchanged. Incremental policy PASS65474entries/2485159760bytes.
No global finite target K/full verification; infinity claim unchanged.
Estimate45%, plausible35–55%, relative to rebased main. Usage27%weekly/
0resetcredits. Continue actual post-state_init main/frame/target composition.


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


## Actual main caller receives the completed payload header

The original run_attempt hdr call now derives its real returned word from
payload_header's actual normal execution. Its actual caller restoration retains
SI/PL, the complete decoded input, all31header-field facts, allocated buffers,
bounded aligned heap and the derived zero transaction/withdrawal counts.
No later hash result, success, funding or extra entry hypothesis is assumed.

The complete original prefix through that call either stops or reaches its
unchanged header-hash continuation within479872711490source ticks. Header
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
comparison continuation within479872713796source ticks. This is not a
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

## Actual optional fields and final list prefix without a record image

The original final list suffix now executes within31source ticks using only
its real reserved18output bytes. Its payload may exceed the old1024byte
record model. Actual scalar subtraction derives the payload; the genuine
list-length helper gives1..9prefix bytes. The real stores and tuple return
derive start in[buffer,buffer+8], positive encoded length and exact output
end at the current cursor. All earlier input words and full metadata survive.
Every outcome obeys the same cost; actual normal returns recover this span
at the caller's actual clock, without future success/funding premises.

The original flag decision is checked even if its read fails or is malformed.
The real optional fixed byte/scalar fields cost81source ticks and advance by
at most50bytes; together with the suffix, every outcome costs≤112. Actual
normal returns derive the final output end in[currentCursor,currentCursor+50]
and retain the whole earlier input prefix. No decoded parent image is assumed.

Validation: current-header-optional-no-image-v3.log PASS1253jobs; all7new
printed facts use permitted axioms. Index8700modules/19032facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to reference main. Weekly
usage42%, no reset credits, ordinary usage allowed. No new candidate paths;
historical untracked WIPs untouched.

Next: connect the full base-field sequence, first actual scoped byte call
and real allocation to finish the arbitrary-read parent-header encoder.
Then actual parent hash/restored header caller, remaining main, uniform
formal target steps, exact K, dominant slack review and cleanup. Source clocks
omit straight-line target work. The original executable stays unchanged.

## Complete original arbitrary-read header encoder

The unchanged base sequence costs43314053799source ticks; its real optional/
list tail makes43314053911. The first scoped32byte writer supplies its real
returned1..41length and actual pointer update, without a successful pointer
read or decoded parent image premise. Including that scoped call gives
43314053973through the body after buffer allocation. Real normal allocation
derives request room, the exact rounded next heap and reserved list bytes.
Every outcome of the complete encoder now costs≤43314053975body source ticks.

A real normal encoder return derives positive encoded length≤33806090619,
start in[buffer,buffer+8], output end≤buffer+33806090619, its actual1024byte
allocation room and next heap, complete metadata and every word below the
buffer unchanged. The encoder itself derives all cursor/frontier conditions.
No decoded parent image, future success or worst-case funding is assumed.
The actual earlier header pointer may alias or fail to read; costs cover it.

Validation: current-header-encoder-no-image-v2.log PASS1257jobs; all12new
printed facts use permitted axioms. Index8700modules/19044facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to reference main. Weekly
usage42%, no reset credits, ordinary usage allowed. No new candidate paths;
historical untracked WIPs untouched.

Next: price the actual parent-header hash using this encoder contract. Its
normal memory proof must support the derived nonwrapping span without an
input-arena oracle: generalize real normal copy-span frames as needed while
retaining the actual owned hash state/pad/output buffers. Then whole restored
header caller and remaining main path; uniform formal target steps, exact K,
dominant slack review and cleanup. Source ticks omit straight-line target
work. The original executable stays unchanged.

## Exact normal copy spans and software hash without input ownership

The actual memcpy loops now derive an exact destination-span frame for any
known count n with n+32<2^64, without source/destination ownership or mapping
premises. The real guard and normal stores derive their bounded cursor and
writes; actual ABI/caller restoration supplies the full ignored-call frame.

The software hash padding copy uses that stronger contract. Its normal
memory proof no longer assumes an input arena, including for the derived
short remainder. The whole hash body needs only n+136<2^64 numerically plus
its actual owned state, pad and output buffers. It still protects every word
outside those actual write spans. A new caller contract exposes this weaker
entry; the old owned-input caller is a compatibility wrapper. Redundant input
subrange/arithmetical facts were removed from the body proof. The real source
reads may fail or wrap; successful normal execution supplies its own reads.

Validation: current-keccak-no-input-arena-v2.log PASS1240jobs; all4new printed
facts and strengthened existing facts use permitted axioms. Index8700modules/
19048facts; inventory8745, replacement closure0, fixed files unchanged.
Incremental policy PASS, 65536package entries. Claim infinity; no global finite
target K/full verifier success. Effort55%, plausible45–65%, relative to main.
Weekly usage42%, no reset credits, ordinary usage allowed. No new candidate
paths; historical untracked WIPs untouched. Source clocks omit straight-line
target work; original executable unchanged.

Next: compose the actual parent-header hash from the arbitrary-read encoder
and weaker normal hash contract, then whole restored header caller/remaining
main, uniform formal target steps, exact K, dominant slack review and cleanup.

## Actual parent hash complete; whole header-validator source cost

The original parent header_hash now costs54251319248body /54251319249caller
source ticks. The actual arbitrary-read encoder return supplies encoded
length≤33806090619; the software hash then costs≤10937265269body ticks, with
its own real call/release tail. Failed reads, ABI checks, allocation and all
hash outcomes are covered; no decoded parent image, owned input span or
future successful/funded execution is assumed.

A genuine normal hash restores its actual saved heap mark and protects the
older input outside the real output/state/pad writes. Its actual caller
retains those facts with real local restoration. The old after-encode normal
helper was strengthened to the numerical length premise and new hash frame.

The unchanged validate_header parent-hash/comparison/release/final-guard tail
now costs54251319379source ticks. Its real earlier451287tick physical prefix
derives that same heap, temporary bindings and typed parent entry. Thus every
outcome of the complete original validate_header costs≤54251770666body ticks.
Normal-return memory/frame and restored main-caller composition remain open.

Validation: current-parent-header-hash-complete-v1.log PASS3102jobs, including
the full earlier main/hash/transaction/header caller graph; all11new printed
facts and strengthened helpers use permitted axioms. Index8700modules/19059
facts; inventory8745, replacement closure0, fixed files unchanged. Incremental
policy PASS, 65536package entries. Claim infinity; no global finite target K/
full verifier success. Effort55%, plausible45–65%, relative to main. Weekly
usage42%, no reset credits, ordinary usage allowed. No new candidate paths;
historical untracked WIPs untouched. Source clocks omit straight-line target
work; original executable unchanged.

Next: derive the real normal parent-comparison/release tail and whole current
validate_header physical frame, restore its main caller, then remaining main,
uniform formal target steps, exact K, dominant slack review and cleanup.

## Complete actual validator normal return and ordinary caller

The real parent comparison retains all nonlocal state and memory, the actual
release restores its saved mark, and a successful final guard reaches the
literal zero return. The real parent hash/compare/release suffix therefore
retains every older input word and all nonheap globals.

Earlier guards and scopes cannot themselves return the enclosing validator.
A genuine final return now exposes both actual fee/ommer prefixes, their
physical memory/global frames, and the real returning parent suffix. The
whole unchanged validator derives zero, original heap restoration and every
older input word outside the actual fixed division workspace. Lexical scope
restoration is transferred through actual prefix execution erasure. No future
successful helper/allocator call or worst-case funding is supplied.

The real ordinary two-word ABI/caller now costs≤54251770667source ticks and
retains those normal heap/global/input facts. The main program still must
supply that actual call's arguments/context and transfer its decoded data/
header facts past the workspace; its remaining continuation is not completed.

Validation: current-header-whole-normal-caller-v1.log PASS3102jobs; all9new
printed facts use permitted axioms. Index8700modules/19068facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage42%, no
reset credits, ordinary usage allowed. No new candidate paths; historical
untracked WIPs untouched. Source clocks omit straight-line target work;
original executable unchanged.

Next: connect the actual main validate_header call, preserve its complete
decoded data and header after the real normal return, then remaining main,
uniform formal target steps, exact K, dominant slack review and cleanup.

## Actual main passes header validation with its physical data intact

Dynamic validator callers now derive the actual parent/header scalar words
from this same ABI lookup; failed reads or wrong shapes are included in the
54251770667tick caller allowance. No separately retained parent image/binding
is required. A real normal call supplies the complete heap/global/input frame.

The main call now retains the full decoded Data and physical AfterHeader
record. All copied input, stateless/payload records and real header cells are
past the640byte arithmetic workspace. Actual workspace slot numbers prove
those protected words are outside every possible division write. The real
incoming heap is restored, caller bindings survive, and all decoded/header
facts are transported using the genuine normal run.

The unchanged main prefix through both indexed tries, requests/BAL/header
hashes, version check and actual complete header-validation caller now either
stops or reaches the original afterValidateHeader continuation within
534124484593source ticks. Actual zero transaction/withdrawal counts and all
physical data/header facts are retained. This is not a whole-main or target K.

Validation: current-main-after-header-validation-v2.log PASS3102jobs; all10new
printed facts use permitted axioms. Index8700modules/19078facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage43%, no
reset credits, ordinary usage allowed. No new candidate paths; historical
untracked WIPs untouched. Source clocks omit straight-line target work;
original executable unchanged.

Next: the actual block-environment allocation/zero/stores, then unchanged
execute_block. Its transaction/withdrawal loops receive the real zero counts,
but mandatory system transactions and block-finalization helpers remain to
be bounded from their actual entries. Continue whole-main completion,
uniform formal target steps, exact K, dominant slack review and cleanup.

## Complete main setup reaches the actual execute_block call

The unchanged block-environment prefix allocates its real120byte be buffer,
zeroes it and performs12literal field stores. Every outcome costs≤156source
ticks, including failed pointer reads, shapes, allocation/zero/store failures
and short clocks. The fixed-length dynamic zero caller needs no pointer image.

A normal ordinary word-store list cannot wrap across the unmapped gap and
write before its initial address. Actual mapped stores derive this fact even
when a read global's flattened value width was not separately retained. Thus
all real be field stores protect earlier input without adding shape or future
read/store-success assumptions. Normal allocation derives room and its exact
new heap/be globals. Actual zero/store prefixes retain full physical decoded
Data/header facts, all caller locals and the owned aligned output buffer.

The original main now either stops or reaches its actual execute_block call
within534124484749source ticks, with zero actual user transaction/withdrawal
counts, complete earlier input/header facts and the real be buffer. Mandatory
system transactions and block-finalization helpers are still unbounded here;
this is not a complete main bound or formal target K.

Validation: current-main-block-environment-entry-v2.log PASS3102jobs; all19new
printed facts use permitted axioms. Index8700modules/19097facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage43%, no
reset credits, ordinary usage allowed. No new candidate paths; historical
untracked WIPs untouched. Source clocks omit straight-line target work;
original executable unchanged.

Next: actual execute_block entry/init and its mandatory system transactions,
using genuine runtime gas/state/table facts and the existing budget library.
Then block-finalization helpers, complete main/source connection, uniform
formal target steps, exact K, dominant slack review and cleanup.

## Original execute_block entry and first output buffer

Main's actual SI/HDR arguments now determine the unchanged executor ABI
(index802). Its two original scalar declarations load the physical SI payload
pointer and the actual payload transaction count at offset40. The retained
decoder image proves that count is zero. Every real executor outcome reaches
the continuation after those declarations with lexical restoration; no fresh
input restriction or successful future call is assumed.

The existing block-environment contract now also retains the actual heap
beyond its120byte allocation. This follows from the same normal allocation
and is preserved through real zero/stores and executor entry. The original
output allocation88 and zero88 cost at most115source ticks together. Actual
normal execution supplies its own allocation room, aligned owned output,
advanced heap and bo binding; it retains the complete earlier input/header,
be ownership/global and real zero ntx local. The whole executor prefix either
stops within115ticks or reaches its original array allocations with those
physical facts. These are source clocks, not a completed executor or target K.

Validation: current-execute-block-body-output-v1.log PASS3102jobs; all12new
printed facts use permitted axioms. Index8700modules/19109facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage43%, no
reset credits, ordinary usage allowed. No new candidate paths; historical
untracked WIPs untouched. Original executable unchanged.

Next: remaining actual executor initialization (arrays, lists, bal_init),
mandatory system transactions and finalization. The original system-message
store is gas30000000, with reservoir97920*16; do not silently apply the
regular transaction16777216 cap. Retain genuine state/table invariants from
real calls as needed. Then complete main/source connection, uniform formal
target steps, exact K, dominant slack review and cleanup. Output/be exact
field images are not separately asserted by the ownership frames yet.

## Whole unchanged executor initialization priced before first system call

The actual persistent lst_new body has two allocations and three stores,
with a4source tick body bound on every outcome. No element-size/capacity or
memory image is assumed. Original bal_init uses three real Patricia table
constructors (8body ticks each), one allocation and a scalar global assignment:
29body ticks,30caller. Generic body pricing now covers global-result calls
with arbitrary actual expressions and failed ABI evaluation/lookup included.

The17actual lexical actions of execute_block before its first mandatory
beacon-roots system transaction now have an all-outcome161source tick bound.
This includes both declarations, output allocation/zero, transaction/receipt
arrays, log/return lists, request array, stores and full bal_init. A syntax
proof identifies the remaining original system call. Every real executor
outcome either stops within161ticks or supplies its genuine prefix execution
and resumes at that continuation. The initial-cost theorem assumes only the
original installed code, without predicting normal returns, memory images,
room or count values. Full runtime state/table models after this prefix are
still to be derived from that retained real execution; the source-cost trace
does not assert they already hold and is not a whole executor or target bound.

Validation: current-execute-block-initial-cost-v2.log PASS3102jobs; all9new
printed facts use permitted axioms. Index8700modules/19118facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage43%, no
reset credits, ordinary usage allowed. No new candidate paths; historical
untracked WIPs untouched. Original executable unchanged.

Next: derive actual post-initialization state/table/field images for mandatory
system transactions, starting with the original beacon-roots call. Its gas is
30000000 and reservoir97920*16, so do not substitute the regular transaction
16777216 cap. Then mandatory calls/finalization, complete main/source,
uniform formal target steps, exact K, dominant slack review and cleanup.

## Actual persistent-list and array normal returns retain their physical data

The original lst_new body now has a full normal-return theorem for arbitrary
scalar size/capacity. Both actual allocation calls derive their own room;
the real wrapped size*cap word is used, without assuming multiplication or
future allocation success. Its actual three stores return the owned aligned
header with backing pointer, zero length and exact capacity. The backing
extent follows the header. A complete persistent frame retains all earlier
memory, every non-heap global and runtime metadata, with an advanced bounded
aligned heap. No initialized backing contents are assumed or needed while
the list is empty.

A real reached scoped list caller now supplies that same empty-list image,
actual returned binding and every other restored caller variable. A matching
actual scoped-array allocation interface supplies its extent, advanced heap
beyond the allocation and complete persistent frame. A reusable executor
OutputBuffer.of_persistent transport retains the whole earlier decoded
Data/header, block environment and zero transaction local through these
actual helper frames, with the caller's genuine retained bindings supplied.

Validation: current-execute-block-list-allocation-callers-v2.log PASS3102jobs;
all7new printed facts use permitted axioms. Index8700modules/19125facts;
inventory8745, replacement closure0, fixed files unchanged. Incremental policy
PASS,65536package entries. Claim infinity; no global finite target K/full
verifier success. Effort55%, plausible45–65%, relative to main. Weekly usage
44%, no reset credits, ordinary usage allowed. No new candidate paths;
historical untracked WIPs untouched. Original executable unchanged.

Next: instantiate these actual normal-call interfaces in the executor's
transaction/receipt arrays and log/return lists, retaining their field images
through the intervening output stores. Derive BAL/state/table facts for the
first mandatory system call. Its gas30000000 exceeds the regular-transaction
16777216 cap in several legacy GasBudget interfaces; broaden the logical
budget interfaces as needed without changing executable code or substituting
that smaller cap. Then remaining mandatory calls/finalization, complete
main/source, uniform formal target steps, exact K, dominant slack and cleanup.

## Original executor reaches log-list setup with both physical arrays

Actual scalar output stores now supply their exact single written word,
unchanged caller locals/globals and every other memory word. Their owned
aligned output addresses are mapped; the real normal store derives its own
state, without predicting any future read or successful call. Such writes
retain the full earlier decoded input/header/block environment and cannot
silently overwrite other newly allocated headers.

The original transaction/receipt allocation expression reads the already
proved zero ntx local, so both actual requests are16bytes. Their reached
normal calls supply room, aligned owned extents, actual named caller
bindings, a complete persistent frame and heap beyond each allocation.
The executor's same four real allocation/store actions now retain both
output pointer fields, caller variables, disjoint ordered16byte arrays and
the advanced heap, together with all earlier Data/header/be/bo facts.

Every array-prefix outcome either stops within4source ticks or reaches the
original log-list constructor with those physical facts. Composing this
with the actual opening declarations/output allocation/zero gives a real
executor prefix of119source ticks to log-list setup. The whole initialization
cost161 remains checked separately; this milestone connects actual physical
invariants through the array stage, not complete system execution/target K.

Validation: current-execute-block-arrays-v1.log PASS3102jobs; all9new printed
facts use permitted axioms. Index8700modules/19134facts; inventory8745,
replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage44%, no
reset credits, ordinary usage allowed. No new candidate paths; historical
untracked WIPs untouched. Original executable unchanged.

Next: connect actual log/return list constructors and output stores, retaining
empty header images and heap beyond backing extents. Then request allocation,
BAL/state/table facts for the first mandatory system call (gas30000000, not
the regular16777216 cap), remaining calls/finalization, complete main/source,
uniform formal target steps, exact K, dominant slack review and cleanup.

## Original executor reaches request allocation with its real empty log list

The actual normal list body/caller now additionally retains the bounded
aligned heap beyond its backing allocation. This is a derived conclusion
from the same actual second allocation, with no added entry premise. It
prevents later fresh persistent allocations from aliasing the live backing
buffer. Both generic list normal interfaces and their earlier callers have
been rechecked with that stronger conclusion.

Real persistent helpers and exact output stores now transport both array
pointer cells, their caller bindings and full earlier physical state. The
original lst_new(8,16) call and bo+40 store supply the exact empty24byte log
header (backing pointer, length0, capacity16), owned128byte backing, aligned
ordered header after both arrays, actual logs binding/output pointer, and a
heap beyond the backing. Every earlier input/header/be/bo/array fact survives
that same real prefix execution; backing contents remain unspecified.

The actual log prefix costs≤5source ticks on every outcome. Composed with
the complete original prefix already connected, execute_block either stops
within124source ticks or reaches its original request allocation with the
full physical log/array/input contract. Whole initialization still has its
separate161tick cost; mandatory system execution and target K remain open.

Validation: current-execute-block-logs-trace-v1.log PASS3102jobs; all7new
printed facts use permitted axioms. Index8700modules/19141facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage44%, no
reset credits, ordinary usage allowed. No new candidate paths; historical
untracked WIPs untouched. Original executable unchanged.

Next: connect real request-array/return-list setup and output stores. Derive
images of untouched zeroed output counters (not yet asserted by the ownership
contracts), then BAL/state/table facts for the first system call. Its original
gas is30000000, above the regular16777216 logical cap in some legacy budget
interfaces. Continue mandatory calls/finalization, complete main/source,
uniform formal target steps, exact K, dominant slack review and cleanup.

## Original request array retains the complete empty log and input state

Later actual persistent helpers now carry the full empty log header,
backing ownership/frontier, output pointer, arrays and decoded input through
their genuine caller-name/memory frames. Exact scalar output stores at other
fields retain that same contract. An owned header beyond the output cannot
alias any scalar output destination; ordinary natural extents prove this
without an input mapping or later success oracle.

The original request expression8*16 evaluates to the actual128byte word.
Its genuine allocation supplies room and an aligned owned128byte request
extent beyond the complete log backing. The real bo+56 store supplies the
actual reqs binding/output pointer while preserving all earlier empty-log,
array/header/input/be/bo facts and the bounded heap beyond the request array.
No initialized request-array contents or zero request-counter image is assumed.

Every request-prefix outcome stops within2source ticks or reaches the
original return-list constructor with this complete physical contract. The
entire actual executor prefix connected so far costs126source ticks. Full
initialization still has its separate161tick cost; system execution and the
uniform formal target-step bound remain open.

Validation: current-execute-block-request-array-v2.log PASS3102jobs; all8new
printed facts use permitted axioms. Index8700modules/19149facts; inventory
8745, replacement closure0, fixed files unchanged. Incremental policy PASS,
65536package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage44%, no
reset credits, ordinary usage allowed. Original executable unchanged.

Next: small proof-module cleanup, then actual return-list/ntx stores and BAL
initialization. Five historical untracked drafts have no external importers
and can be preserved outside the candidate before splitting this now-large
proof module. Derive untouched zeroed output counters and real state/table
facts before system execution (gas30000000, above legacy regular16777216
interfaces), then finalization, complete main/source, uniform formal target
steps, exact K, dominant slack review and cleanup.

## Proof-module cleanup and four freed candidate paths

Moved the already checked1413line ExecuteBlock namespace section from
CurrentVerify/TransactionData.lean to CurrentVerify/BlockExecution.lean,
which imports TransactionData. The moved declaration bytes are identical;
all theorem names, assumptions, statements and proofs are preserved. The
original input/header/main setup remains in TransactionData. Future executor
proof edits can rebuild the smaller BlockExecution module while reusing its
unchanged setup dependency.

Five historical untracked draft modules were not imported outside their
own draft set: RlpLength/BeCurrent and RlpWrite/HeaderCurrentCost,PutBeCost,
PutBeNormal,WriteFrame. Their382lines are preserved locally with SHA256
manifest under work/agent-notes/wip-archive/2026-10-30-block-execution-split/,
outside the candidate and this commit. No live import was removed. Archiving
five unused candidate files and adding the new proper proof module reduces
the candidate by four entries. No executable or fixed proof source changed.

Validation: current-block-execution-module-split-v1.log PASS3103jobs; all
moved/current facts retain permitted axioms. Index8701modules/19149facts;
inventory8741, replacement closure0, fixed files unchanged. Incremental policy
PASS,65532package entries. Claim infinity; no global finite target K/full
verifier success. Effort55%, plausible45–65%, relative to main. Weekly usage
44%, no reset credits, ordinary usage allowed.

Use the selected root InitECandidate.Solver.Input.CurrentVerify.BlockExecution
for subsequent executor work, still with artifact cache disabled, the two-slot
limited-lake/resource wrapper and the8GiB cap. The actual executor prefix
currently reaches return-list setup within126source ticks, retaining request
extent, complete empty-log/array/input facts and the actual advanced heap.
Next: original return-list/ntx stores and BAL initialization, untouched zeroed
output-counter images, real state/table facts for system execution (gas30000000,
above several legacy regular16777216 interfaces), then finalization, complete
main/source, uniform formal target steps, exact K, dominant slack and cleanup.

## Original executor reaches BAL with both real empty lists and output count

Later actual persistent calls and exact scalar stores now retain the complete
request extent/output pointer as well as the existing empty-log/array/input
contract, using actual caller-name and memory frames. The original rls
constructor supplies an aligned owned24byte header and128byte backing after
the request array, with exact pointer/length0/capacity16 fields and heap beyond
the backing. Its real bo+72 store and original ntx store at bo+80 retain those
fields and every preceding request/log/array/header/input/be/bo fact. The
stored transaction count is the actual already-proved zero word; no new
future-success, room, count or initialized-backing premise is introduced.

Every return-list-prefix outcome either stops within5source ticks or reaches
the original BAL initializer with that full physical contract. The complete
actual executor prefix connected so far therefore costs131source ticks.
The independent all-outcome whole-initialization cost161 remains checked;
BAL physical initialization, mandatory system execution and target K are open.

Validation: current-execute-block-return-list-v1.log PASS3103jobs; all7new
printed facts use permitted axioms. Index8701modules/19156facts; inventory
8741, replacement closure0, fixed files unchanged. Incremental policy PASS,
65532package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage44%, no
reset credits, ordinary usage allowed. Original executable unchanged.

Additional compatibility evidence: current Guest.Software.guestFn_htab_new_scratch
allocates88bytes and current htab_get calls htab_find_leaf (Patricia tables).
The older ScratchTable.Program.actions allocates72bytes. Several legacy
GasBudget/root-frame interfaces use that older table model, so their actual
code/model entry requirements must be ported before use, alongside the
already-known system gas30000000 versus regular16777216 cap. Do not assume
these older interfaces instantiate on the current code just because they
were previously checked. Pure arithmetic/rank results may still be reused.

Next: real BAL global-result table/allocation calls and zero bal_index,
retaining this complete physical state. Then untouched zeroed output-counter
images and actual state/table facts, current-code system gas/table interfaces,
mandatory calls/finalization, complete main/source, uniform formal target
steps, exact K, dominant slack review and cleanup. Selected executor root is
InitECandidate.Solver.Input.CurrentVerify.BlockExecution; retain two workers,
artifact cache disabled and8GiB resource cap. Four candidate path slots remain.

## Current BAL global-result table and caller-transport interfaces

The current Patricia constructor's real normal return now supplies its own
88byte header arena, persistent callee frame before the global assignment,
exact global-result update and heap beyond the complete header. No old global
destination value/shape or allocation room is required at entry. The header
frontier follows the actual first88byte allocation and a checked heap-
monotone proof for all remaining original constructor syntax/allocations;
it does not substitute a different table constructor or assume later success.

The callee-scope table_global_memory_normal interface needs only the actual
runtime arena, incoming bounded/aligned heap and actual scalar arguments.
It supplies restored caller locals, the assigned global header, owned88byte
extent, runtime arena, complete earlier-memory frame, advanced heap beyond
the header, and all globals except that destination and heap retained. This
fits BAL's no-argument callee scope, where main's SI/HDR/array/list locals are
absent. It supports the actual20/28/60byte keys and64capacity via the checked
current scalar-constructor normal theorem; table contents/models beyond the
owned header are not additionally asserted here.

ReturnList physical facts now transport across genuine persistent helpers,
protected global updates and a full PersistentMemoryFrame with separately
retained input globals. The latter restores the actual outer caller's
bindings after BAL returns, while allowing BAL's own globals to change and
the real heap to advance. Do not assume main's ReturnList holds inside BAL's
callee locals. All decoded/header/array/request/empty-list/owned-buffer and
output-cell facts follow their actual frame; no future callee success is an
entry hypothesis for the all-outcome cost result already proved.

Validation: current-execute-bal-table-assignment-v1.log PASS3103jobs; all8new
printed facts use permitted axioms. Index8701modules/19164facts; inventory
8741, replacement closure0, fixed files unchanged. Incremental policy PASS,
65532package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage44%, no
reset credits, ordinary usage allowed. Original executable unchanged.

Next: compose BAL's actual three global table calls, global64byte allocation,
zero bal_index and return using arena/heap memory frames in its own scope.
Preserve the five BAL globals and unrelated globals explicitly; then invert
the actual ordinary BAL caller and use ReturnList.of_memory_frame once on
its genuinely restored caller locals. The connected executor prefix remains
131source ticks to BAL; its independent161tick whole-initialization cost is
already checked, but the complete BAL physical result is not yet connected.
Then untouched zeroed output counters and actual state/table facts, current
scratch-table/gas interfaces (88byte current headers versus72byte legacy,
system gas30000000 versus regular16777216), mandatory calls/finalization,
complete main/source, uniform formal target steps, exact K, dominant slack
review and cleanup. Selected root remains CurrentVerify.BlockExecution with
two workers, artifact cache disabled and8GiB cap; four path slots remain.

## Whole original executor initialization reaches first system call physically

The actual BAL command sequence now has a full physical execution proof in
its own callee scope: three current Patricia constructors at20/28/60byte keys
and capacity64, the real64byte bal_key_buf allocation, then bal_index=0. Each
next cursor, owned88byte table header, allocation room and bounded/aligned
heap follows from the same observed normal call. All three table-header
regions and the key buffer are ordered/disjoint; the final five BAL globals
have their actual returned words. Runtime arena, complete memory before the
incoming heap, caller locals and every global outside BAL's destinations/
heap are retained. Table entry contents/models beyond owned header geometry
are not additionally asserted by this contract.

The complete BAL body returns the actual zero word and retains that result
through its original return. Its real ordinary caller restores the executor's
own bindings and uses the genuine memory frame/retained globals to recover
all input/header/be/bo/array/request/empty-log/empty-return-list facts. The
actual trailing skip reaches the original first mandatory system call with
those same physical facts and initialized BAL allocations. No main-local
bindings inside the no-argument BAL callee are assumed.

Every BAL caller outcome costs≤30source ticks, including failures/timeouts.
The connected original executor prefix now either stops within161source
ticks or reaches beforeFirstSystem with full BalReady physical state. This
matches the previously independent whole-initialization cost, now joined to
the actual runtime state. Mandatory system execution, finalization and the
uniform formal target-step bound remain open; this is not global target K.

Validation: current-execute-first-system-physical-v1.log PASS3103jobs; all14new
printed facts use permitted axioms. Index8701modules/19178facts; inventory
8741, replacement closure0, fixed files unchanged. Incremental policy PASS,
65532package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage45%, no
reset credits, ordinary usage allowed. Original executable unchanged.

Next: derive untouched zeroed output counters and actual runtime state/table
images needed by the first mandatory beacon-roots system call. Use current
Patricia/scratch-table interfaces (88byte headers, not legacy72byte models)
and actual system gas30000000/reservoir97920*16, not regular16777216 root
caps. Retain the actual original prefix executions when obtaining stronger
field/table images; ownership alone does not assert contents. Then remaining
mandatory calls/finalization, complete main/source, uniform formal target
steps, exact K, dominant slack review and cleanup. Selected root remains
CurrentVerify.BlockExecution, cache disabled/two workers/8GiB cap; four
candidate path slots remain. Full executor-initialization code remains the
original Guest.Software.guestFn_execute_block and guestFn_bal_init.

## Actual output-clear image survives all executor initialization

The pre-clear allocation now has its own OutputAllocation ownership contract;
only the real successful memzero yields OutputBuffer with initialized fields.
The exact normal aligned Zero.call_normal theorem derives its own clock
funding by the checked clock-padding proof, so no minimum/future clock is
added to the entry assumptions. Its canonical memory image and the generic
zero-word theorem supply the actual zero words at bo offsets0,8,16,48,64.

Those untouched fields are now part of the initialized output contract.
Actual later persistent allocations and BAL's genuine memory frame retain
them below the incoming frontier. All six original scalar output stores are
at other fixed fields; their exact one-word footprints prove preservation.
Protected global updates retain the same memory image. All existing array,
log, request, return-list, BAL body/caller and complete first-system-entry
proofs have been rebuilt with the stronger initialized-state contract.

BalReady.initial_zero_fields exposes the five exact words at the genuine
first mandatory system call, including the previously unasserted request
counter at bo+64. The transaction-count word at bo+80 remains independently
proved by its actual original ntx store. The connected initialization bound
is still161source ticks, on every outcome. This does not assert that these
initial fields remain zero after system execution modifies the output.

Validation: current-execute-output-zero-counters-v2.log PASS3103jobs; all3new
printed facts use permitted axioms, and all strengthened existing physical
results retain permitted axioms. Index8701modules/19181facts; inventory8741,
replacement closure0, fixed files unchanged. Incremental policy PASS,
65532package entries. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to main. Weekly usage45%, no
reset credits, ordinary usage allowed. No new candidate paths. Original
executable unchanged.

Next: current scalar Patricia constructor/table-state images and genuine
runtime state needed by the beacon-roots system call, including20/28/52/60
byte keys rather than only32byte witness hashes. Current scratch headers are
88bytes (legacy72byte models do not instantiate); actual system gas30000000
and reservoir97920*16 must not be replaced by regular16777216 caps. Then
mandatory calls/finalization, complete main/source, uniform formal target
steps, exact K, dominant slack review and cleanup. Keep the selected
CurrentVerify.BlockExecution root, cache disabled/two workers/8GiB cap;
four candidate path slots remain.

## Actual scalar Patricia constructor and initialized BAL table images

The unchanged current htab_new now has an exact normal-result proof for
arbitrary scalar key widths and capacities at least two. The same observed
execution supplies all four allocation requests' room and four paid source
clock ticks. Its canonical nonlocal result includes the eleven real stores,
exact backing pointers and final allocator cursor. The88byte header's
persistent request room is retained separately from ordinary mapped Arena
ownership; the latter has a different, larger ceiling and is not a substitute.

ScalarGeometry records the actual word-sized allocation extents, alignment
and ordering. ScalarEmpty records those owned arrays and the initialized
header, without treating uninitialized backing cells as live nodes. Larger
natural-number size formulas still require their own no-overflow facts.
Exact memory/nonlocal frames and genuine earlier-memory persistent frames
transport this image. The original ordinary global-result htab_new call
recovers its actual callee bindings/return and retains the same image.

The three actual bal_init calls now establish empty images for20/28/60byte
keys at capacity64. Their genuine later allocation frames retain all earlier
header fields through the key-buffer allocation and bal_index assignment.
BalCells carries these three images. Its return/caller transport now uses a
full nonlocal equality, since equality of globals alone cannot retain table
memory contents. The complete existing initialization proofs have been
rebuilt with this stronger contract, including the actual first-system-call
entry. The connected initialization cost is still161source ticks; mandatory
system execution and whole-program target K remain open.

Validation: current-scalar-table-image-v6.log PASS754jobs;
current-execute-scalar-table-images-v2.log PASS3104jobs. All13new printed
facts and the renamed/strengthened existing results use permitted axioms.
Index8702modules/19194facts; inventory8742, replacement closure0, fixed
files unchanged. The obsolete BalCells.of_globals index entry was removed
when its stronger of_erase replacement was recorded. Incremental policy
PASS65533package entries/2488363848bytes; this is not full verification.
Claim infinity; no global finite target K or full verifier success.
Effort55%, plausible45–65%, relative to reference main. Weekly usage45%,
no reset credits, ordinary usage allowed. Original executable unchanged.

Next: genuine initial/runtime state and current Patricia lookup/update
images needed by the first mandatory beacon-roots system call, including
20/28/52/60byte keys. Extend the current representation beyond the32byte
witness model; scratch headers are88bytes, not legacy72byte headers. Keep
actual system gas30000000 and reservoir97920*16. Then remaining mandatory
calls/finalization, complete main/source, uniform formal target steps,
explicit K, dominant slack review and final unused-code cleanup. Selected
root remains CurrentVerify.BlockExecution, cache disabled/two workers/8GiB
cap. One new Solver module uses one of the four previous candidate path
slots; three remain after the successful incremental policy check.

## Runtime scalar empty lookup and actual fresh-transaction prefix

The unchanged htab_find_leaf header prefix now derives keybits from its
actual arbitrary scalar key width, with all original declaration scopes.
An empty ScalarEmpty image then proves a literal zero return, zero body
source ticks even at clock0, and the complete nonlocal frame. Neither query
byte mapping nor initialized node-array cells are required. The original
scoped caller retains its genuine continuation and one-call-tick allowance;
an enclosing normal return cannot use the cheap stopped branch instead.

The complete unchanged htab_get now has the corresponding arbitrary-width
empty-table result: at most1body source tick on every outcome, literal
absentValue on each genuine normal return, exact normal clock decrement
and the full physical frame. Ordinary/scoped get callers cost at most2,
including failures/short clocks; their real absent result/continuation are
retained. These results are instantiated from the actual20/28/60byte BAL
images at the original first-system-call entry, for unrestricted scalar
query pointers. This is an initial empty-table result, not an invariant
for later nonempty tables or updates.

The actual original state_fresh_tx at index321 now costs at most74body /
75caller source ticks on every outcome. The proof uses its unchanged72byte
record allocation, eight current Patricia constructors at the actual key
widths/capacities, all nine record stores and the journal_n reset. No old
hash-map constructor or future allocation-room premise is substituted.
The opening of the actual unchecked system-transaction body now either
stops within75source ticks or reaches its unchanged ext_code_of continuation
with a genuine prefix execution, forward clock and full scope observation.
The fresh transaction's normal physical record/table images still need to
be derived; this new trace proves the actual prefix cost, not those images.

Validation: current-scalar-empty-lookup-v1.log PASS1317jobs;
current-execute-scalar-lookup-and-fresh-v2.log PASS3105jobs. All13new printed
facts use permitted axioms. Index8703modules/19207facts; inventory8743,
replacement closure0, fixed files unchanged. Incremental policy PASS,
65534package entries/2488387851bytes, not full verification. Claim infinity;
no global finite target K or full verifier success. Overall effort55%,
plausible45–65%, relative to reference main. Weekly usage45%, no reset
credits, ordinary usage allowed. Original executable unchanged.

Next: actual normal fresh-transaction record/table images and retained
initial block/workspace state needed for ext_code_of/get_account. Extend
current lookup/update models to nonempty20/28/52/60byte runtime tables and
the current88byte scratch representation. Retain actual system gas30000000
and reservoir97920*16. Then mandatory calls/finalization, complete main /
source bound, uniform formal target steps, explicit K, dominant slack review
and final unused-code cleanup. Selected root remains
CurrentVerify.BlockExecution, cache disabled/two workers/8GiB cap. One new
ScalarLookup module uses one further candidate path; two slots remain.

## Complete actual fresh-transaction record/table images and system entry

The current scalar constructor now has a local-result normal interface
that retains its exact empty image, final allocator cursor and complete
persistent caller frame. Header address bounds and the real final heap
extent let subsequent record stores/allocations protect those images.

FreshTransactionMemory proves the entire unchanged state_fresh_tx normal
result. Its forward Context retains the actually allocated72byte record,
block-state pointer at offset0, live bounded/aligned heap, every completed
record/table image, full earlier-memory frame and all globals outside the
real heap_ptr/ts/journal_n destinations. Each next actual constructor derives
its own room; each actual pointer store preserves the already completed
fields/headers. The real final reset and zero return retain all eight empty
current Patricia tables for20/32/52byte keys and capacities64/16. No empty
backing-array contents, old hash-map model, future successful call or extra
clock/room premise is assumed.

The ordinary ignored fresh-state caller restores the real caller locals
and relates the same memory/globals back to its actual entering state.
The original unchecked system-transaction signature at index794 and its
ext_code_of continuation are now identified. Its genuine first command
therefore either stops within75source ticks or reaches that continuation
with the complete new transaction-state Context, zero journal_n and caller
bindings. This proof uses only legitimate incoming arena/heap invariants
and a typed scalar bs global. Deriving/retaining the latter and full block/
workspace models from actual main/state_init remains required; it is not
silently added to the final certificate's assumptions. The earlier74body /
75caller all-outcome source allowance is unchanged.

Validation: current-fresh-state-complete-v1.log PASS3106jobs;
current-system-fresh-physical-v2.log PASS3106jobs. All21new printed facts
use permitted axioms. Index8704modules/19228facts; inventory8744,
replacement closure0, fixed files unchanged. Incremental policy PASS,
65535package entries/2488424512bytes, not full verification. Claim infinity;
no global finite target K or full verifier success. Overall effort55%,
plausible45–65%, relative to reference main. Weekly usage46%, no reset credits,
ordinary usage allowed. Original executable unchanged.

Next: retain the actual initialized block/workspace state (including bs/ws,
their table images, key scratch and journal allocation) through main/header/
executor initialization into the system callee. ext_code_of calls get_account,
whose first get_account_optional action is htab_set on the fresh20byte
account-access table at ts+8, followed by the empty lookup at ts+16. Prove
that actual current insertion and its frame, then pre-state account/code
access and the remaining mandatory system work. Nonempty runtime table
models and88byte scratch tables remain open. Keep actual system gas30000000
and reservoir97920*16, then finalization, complete main/source, uniform
formal target steps, explicit K, dominant slack review and final cleanup.
Selected root is now CurrentVerify.FreshTransactionMemory (imports the
checked BlockExecution root); cache disabled/two workers/8GiB cap. One new
Solver module consumes one of the two previous candidate path slots; one
slot remains. Archive only genuinely unused drafts outside the candidate
if another split needs room, retaining their exact local bytes as before.

## Actual block/workspace records retained at main's payload_header entry

State initialization's actual normal suffix now retains its MemoryContext,
instead of dropping that context to only ArenaState at the return boundary.
WorkspaceContext carries the actual aligned40byte workspace region and the
heap beyond it. The real bs allocation derives its aligned80byte region,
workspace-before-block ordering, and heap beyond the full block record.
Every later real table call, store, scratch/journal allocation and global
reset retains those facts. Persistent preservation uses the actual incoming
heap cell when transferring its record-frontier bounds.

The complete unchanged state_init normal execution now exposes its actual
ws/bs global values, both owned regions, ordering, bounded/aligned current
heap and older-memory frame. Its input contract is unchanged; all new facts
come from the same real allocations and suffix, including their derived
room. The existing state_init_normal_memory signature is retained as a
projection of this stronger normal result.

StateInitReturned.records now recovers those same records at main's genuine
saved-caller continuation, plus the pre-workspace witness-memory frame and
its actual entering heap cell. The new complete main prefix retains this
contract after state_init. Transaction scanning's actual full nonlocal
frame is also exposed without changing the existing scan API; the stronger
main trace transports both record context and older-memory frame to the
original payload_header entry. Its complete source allowance remains
3387552531on every outcome, with the same actual continued execution and
stopped branches. No separately assumed successful future call is used.

These record facts prove typed globals/ownership/order, not initialized
block/workspace field contents or table models. Those contents, key scratch
and journal properties still need explicit retention/derivation. In
particular, the typed bs entry condition of the fresh-transaction theorem
is now derived from actual main/state_init at payload_header entry; it must
still be transported through the later header/validator/executor prefix.

Validation: current-main-state-records-v1.log PASS3106jobs;
current-main-payload-header-state-records-v1.log PASS3106jobs. All8new printed
facts and all strengthened existing normal results use permitted axioms.
Index8704modules/19236facts; inventory8744, replacement closure0, fixed
files unchanged. Incremental policy PASS65535package entries/2488438182bytes,
not full verification. Claim infinity; no global finite target K or full
verifier success. Effort55%, plausible45–65%, relative to reference main.
Weekly usage46%, no reset credits, ordinary usage allowed. Original
executable unchanged. No new candidate paths; one path slot remains.

Next: retain these real records through payload_header/header validation /
executor initialization and recover actual initialized block/workspace
fields/tables, scratch and journal. CurrentVerify.PayloadHeaderEntry.HeaderFrame
already retains all nonheap globals and older memory below its real header
frontier (lower2701134824); expose/use the actual normal header frame rather
than introduce bs/ws premises at main. Then current20byte account-access
insertion at ts+8, empty lookup at ts+16 and pre-state account/code access.
Nonempty runtime models and88byte scratch tables remain open. Keep actual
system gas30000000/reservoir97920*16; finish mandatory calls/finalization,
complete main/source, uniform formal target steps, explicit K, dominant
slack review and final unused-code cleanup. Selected root remains
CurrentVerify.FreshTransactionMemory, cache disabled/two workers/8GiB cap.

## Actual initialized records retained through complete header validation

The real header-entry heap is now retained in PhysicalHeader instead of
being discarded. A composable StateFrame follows the actual normal header
execution: it preserves nonheap globals except the genuine wd_rlp_slices
assignment, and older memory above the fixed640byte arithmetic workspace
(2701135464) and below the actual entering header heap. Hash/arithmetic
workspaces may change. No future allocation, hash, trie or main success
is assumed. Existing length and transaction normal transfers retain that
same entering heap.

Actual withdrawal setup, loop and indexed-root normal results now expose
their already-proved global frames. The real request encoder, request hash,
BAL hash, return and enclosing scopes retain and compose their actual
older-memory/global frames. Complete normal payload_header execution now
supplies StateFrame at its true return, with the earlier physical/cost API
kept as a projection. Main's actual saved-caller continuation retains the
same frame, original/current MemoryContexts and pre-workspace witness frame.
Its complete stopped/reached prefix remains479872711490source ticks.

The subsequent real header-hash allocation/call, comparison, version guard
and header validator now also expose composable preservation results.
The complete main prefix through actual header validation retains the real
ws/bs global values, owned40/80byte regions, ordering, current bounded aligned
heap and earlier state/input memory. Its all-outcome source allowance is
unchanged534124484593. Division's actual640byte workspace exclusion is
proved from slot numbers; no arithmetic or cryptographic oracle is used.
Initialized record field contents/table models still require explicit
exposure from state_init; this context alone does not claim those images.

Validation: current-header-state-frame-v2.log PASS3106jobs;
current-header-state-return-v3.log PASS3106jobs;
current-header-validation-state-records-v1.log PASS3106jobs. New complete
normal/caller/state results and unchanged downstream roots print only the
permitted axioms. Index8704modules/19257facts; inventory8744, replacement
closure0, fixed files unchanged. Incremental policy PASS65535package
entries/2488467042bytes, not full verification. Claim infinity; no global
finite target K/full verifier success. Effort55%, plausible45–65%, relative
to reference main. Weekly usage46%, no reset credits, ordinary usage allowed.
Original executable unchanged. No new candidate paths; one slot remains.

Next: retain actual ws/bs and earlier state memory through block-environment
allocation/stores and execute_block initialization into the first system
callee. Then expose actual initialized state fields/table images, current
20byte account-access insertion at ts+8, empty lookup at ts+16 and pre-state
account/code access. Nonempty runtime models and88byte scratch tables remain
open. Keep actual system gas30000000/reservoir97920*16; finish mandatory
calls/finalization, complete main/source, uniform formal target steps,
explicit K, dominant slack review and final unused-code cleanup. Selected
root remains CurrentVerify.FreshTransactionMemory, cache disabled/two
workers/8GiB cap. No full verifier or Solution root build on this host.

## Actual initialized state retained to execute_block entry

A smaller RetainedRecords contract carries the actual MemoryContext,
bs-record-end-before-original-header ordering and earlier-memory interval
above2701135464, while allowing later helpers to initialize unrelated
globals. It is derived from the already checked actual header StateFrame
and original record context; it supplies no successful future execution.
Generic actual metadata/heap/global/memory transfers retain that context.

The real block-environment global allocation derives its own allocation
room and retains ws/bs and all older state memory. Actual zeroing and every
literal field store retain that same region. Their real finite normal
store-prefix execution composes those facts; existing physical-only APIs
remain projections. The complete unchanged main prefix to its actual
execute_block entry now also retains the initialized state context and
pre-workspace witness frame, with the same534124484749source allowance
for every outcome. Initialized state field/table contents still need
explicit derivation/exposure from state_init, and the context must still
cross execute_block's161tick initialization into the first system callee.

Validation: current-main-block-env-state-records-v1.log PASS3106jobs; all11
new printed results and downstream roots use permitted axioms. Index8704
modules/19268facts; inventory8744/replacement closure0/fixed files unchanged.
Incremental policy PASS65535package entries/2488479224bytes, not full
verification. Claim infinity; no global finite target K/full verifier
success. Effort55%, plausible45–65%, relative to reference main. Weekly
usage46%, no reset credits, ordinary usage allowed. Original executable
unchanged. No new candidate paths; one slot remains. Next: carry records
through actual executor initialization/BAL and derive the real typed bs
entry of its first fresh transaction, then initialized state field/table
images, account-access insertion/pre-state/code access, all mandatory
system calls/finalization and uniform formal target-step composition.
Dominant slack review and final unused-code cleanup remain in the plan.

## Actual initialized records retained through complete executor initialization

The actual execute_block opening declarations, output allocation and zero
now carry RetainedRecords. Persistent helpers use the observed entering
heap cell and current physical heap floor; output stores derive their
scalar destination/read from the same real store and protect the earlier
state interval. The common transfers retain actual ws/bs, owned records,
ordering, bounded/aligned heap and earlier contents without assuming later
allocation/copy/store success.

Both real array allocations/stores, log-list creation/store, request-array
allocation/store and return-list creation/two stores compose these frames.
The actual BAL initializer may reset its own globals; its separately
checked outside-BAL frame preserves ws/bs and its actual older-memory
frame preserves the earlier initialized state. Complete actual body
traces now retain that context up to beforeFirstSystem on every reached
outcome, with the original161source allowance including stopped outcomes.
The physical-only APIs remain projections of the stronger checked results.

UncheckedSystem.fresh_records_trace derives its actual entering heap and
typed bs global from the retained MemoryContext. It invokes the existing
real fresh-transaction physical proof and reaches ext_code_of with the
actual72byte transaction record/eight empty tables, journal_n0 and callee
locals. Its all-outcome75source allowance is unchanged. At actual callee
entry, MemoryContext.of_frame handles the callee's own local environment.
Initialized bs/ws field/table contents still require explicit exposure
from state_init and retention/recovery in the account/code models; the
context alone is not a field-content proof. No whole system/VM/main bound
or target K is claimed.

Validation: current-executor-output-state-records-v1.log PASS3106jobs;
current-executor-lists-state-records-v1.log PASS3106jobs;
current-executor-bal-state-records-v1.log PASS3106jobs;
current-executor-system-state-records-v1.log PASS3106jobs. All24new printed
results and downstream roots use permitted axioms. Index8704modules/19292
facts; inventory8744/replacement closure0/fixed files unchanged. Incremental
policy PASS65535package entries/2488511116bytes, not full verification.
Claim infinity; no global finite target K/full verifier success. Effort55%,
plausible45–65%, relative to reference main. Weekly usage47%, no reset
credits, ordinary usage allowed. Original executable unchanged. No new
candidate paths; one slot remains.

Next: current20byte account-access insertion at fresh ts+8, then empty
account-cache lookup at ts+16 and real pre-state/code work. Existing
NewNode.Context/no-grow execution is already width-independent and can be
derived from ScalarEmpty. Existing NewLeaf.Fields/model hard-code32byte
keys/256bit leaf markers, so port its actual scalar key copy/leaf stores
and first insertion rather than assume the32byte model for20byte data.
Expose actual initialized bs/ws field/table/scratch/journal images as
needed by these real paths. Keep mandatory system gas30000000 and
reservoir97920*16; finish all mandatory calls/finalization, complete main/
source and uniform formal target steps, explicit K, dominant slack review
and final unused-code cleanup. Selected root remains
CurrentVerify.FreshTransactionMemory; cache disabled/two workers/8GiB cap.

## Actual first20byte account-access insertion cost

The new scalar first-insertion proof follows the unchanged htab_set and
htab_new_leaf bodies at their actual constructor key width. ScalarEmpty
supplies the real free-list/next-index/capacity facts to the existing
width-independent no-grow node allocator. Its actual metadata increment
preserves the key-length, stride and key-array reads. The actual copy
arguments use that width/stride; CopyAny prices every memcpy outcome
without pointer mapping, alignment, key-byte image or future successful
copy premises. All remaining leaf/order/count writes and root return are
checked finite straight-line source work.

The complete real first setter costs CopyAny.price(key.toNat)+4body ticks
and +5ordinary caller ticks when key.toNat+32<2^64, which is derived from
each real small runtime width. In particular the actual20byte insertion
costs≤29caller source ticks, with all setup/copy failures and timeouts
included. CurrentVerify.AccountAccess proves the original Software
get_account_optional opening shape and derives its same-run table/read/
arguments from the actual FreshTransaction.Context at ts+8. No32byte key
model, preinitialized key bytes or successful later insertion is assumed.

Cleanup moves the width-independent empty-leaf branch/no-fallthrough
facts into the basic Set.Guards module. The existing32byte insertion API
still imports those same facts and was checked alongside the new scalar
root. One new candidate module Set.Scalar uses the final existing package
path slot. No executable/ROM/fixed proof bytes changed.

Validation: current-scalar-empty-leaf-v4.log PASS1277jobs;
current-scalar-empty-set-v2.log PASS1359jobs;
current-first-account-access-set-v2.log PASS3108jobs (current main/fresh
root and existing EmptyCost compatibility). All14new printed facts and
unchanged downstream results use permitted axioms. Index8705modules/19306
facts; inventory8745/replacement closure0/fixed files unchanged. Incremental
policy PASS65536package entries/2488537581bytes, not full verification.
Claim infinity; no whole-system/VM/main source bound or finite target K/full
verifier success. Effort55%, plausible45–65%, relative to reference main.
Weekly usage47%, no reset credits, ordinary usage allowed. At the package
entry cap now; add future facts in existing modules or archive genuinely
unused drafts with exact local bytes retained before adding another path.

Next: prove the real first insertion's successful memory footprint and
singleton fields/rank at20byte keys, so the separate ts+16 account-cache
image is retained for its empty lookup and subsequent pre-state/code work.
Generalize nonempty traversal rank to the actual runtime key-bit limits
(160/224/256/416/480), retaining only structural facts needed by the bound
where full key-byte/routing semantics are unnecessary. Actual memory/
allocator/caller connections still must be proved; no future-success
premises are permitted. Expose initialized bs/ws fields/table/scratch/
journal models as needed by the real system paths. Keep mandatory gas
30000000/reservoir97920*16; finish all mandatory calls/finalization, complete
main/source and uniform formal target steps, explicit K, dominant slack
review and final unused-code cleanup. Selected main root remains
CurrentVerify.FreshTransactionMemory; cache disabled/two workers/8GiB cap.

## Complete first scalar insertion frame and actual account-cache miss prefix

FreshTransaction.Context now retains the complete constructor end of every
finished table and pairwise separation of all its actual table regions,
including key/node/order backing allocations. Every real constructor uses
the previous live heap to establish separation from earlier regions; real
pointer stores, later allocation, journal reset and lexical/caller frames
retain it. No pairwise disjointness is assumed as an unexplained main entry
condition. Actual table pointers and other-header words have checked
separation projections.

The first scalar leaf now has a complete actual normal execution proof.
The real no-grow node call yields its exact metadata increment and node1;
the two original declarations expose the actual variable-length copy.
CopyAny's real normal caller supplies a span frame and saved locals. Its
constructor-derived key region preserves header fields and every word
outside the complete table region. The original six leaf/order/count stores
use real scalar node/order arrays and marker key*8 (160for20byte keys).
Their actual mapped addresses and scalar values derive the normal node1
return and full memory footprint. Natural key-width≤60/capacity≤2^32 facts
are instantiated by the actual small constructor constants; no successful
future copy, store or allocation is an entry premise. Metadata simplification
uses an explicit memory-only model lemma instead of expensive implicit
unfolding. Copy-argument derivation is shared with the existing cost proof.

The genuine setter's zero-leaf branch, actual leaf caller and root store
now compose that same normal frame through all declaration/caller scopes.
The complete ignored first-set caller retains all globals/heap, caller
locals and every word outside its actual constructor region. Successful
AccountAccess insertion then retains all seven other fresh table images,
actual transaction fields, complete earlier-memory frame and region
separation. The modified access table is excluded from the remaining
empty-image context, rather than asserted empty again.

The real get_account_optional340 ABI retains the same context at its own
callee entry. Its genuine first setter still costs≤29source caller ticks.
The following actual ts+16 cache lookup derives its image/arguments from
the retained transaction, returns the literal absent pair and retains all
nonlocal fields. The actual cache guard then selects the pre-state call.
Complete to_pre_state either stops within31source ticks (with no returned
value) or reaches that exact unchanged continuation with the remaining
seven images, actual address local, paid/forward clock, full scope frame
and earlier persistent state. No pre-state call or future success is assumed.

Validation: current-fresh-table-regions-v1.log PASS3108jobs;
current-scalar-first-key-region-v1.log PASS3108jobs;
current-scalar-leaf-copy-trace-v1.log PASS3108jobs;
current-scalar-leaf-copied-state-v1.log PASS3108jobs;
current-scalar-leaf-stores-v2.log PASS3108jobs;
current-scalar-first-set-frame-v2.log PASS3108jobs;
current-first-account-cache-miss-v3.log PASS3108jobs. All40new checked facts,
stronger existing context results and unchanged downstream roots print
permitted axioms. Index8705modules/19346facts; inventory8745/replacement
closure0/fixed files unchanged. Incremental policy PASS65536package entries/
2488618276bytes, not full verification. Claim infinity; no whole-system/VM/
main source bound or finite target K/full verifier success. Effort55%,
plausible45–65%, relative to reference main. Weekly usage47%, no reset
credits, ordinary usage allowed. No new paths; at the package entry cap.

Next: get_pre_state_account_optional372 begins by repeating htab_set on
the already nonempty ts+8 table, before its bs+16 lookup and world-state
access. Derive the first insertion's singleton header/node rank facts and
actual nonempty scalar traversal/update/insertion bounds. Runtime leaf
markers use the real key-bit widths160/224/256/416/480; carry structural
rank/footprint facts wherever full key-byte/routing semantics are unnecessary.
Later growth needs actual relocated buffer geometry; the first-constructor
region frame is not a general grow model. Expose/retain initial bs/ws field,
table, scratch/journal and world-root facts for real pre-state/code paths.
Keep mandatory gas30000000/reservoir97920*16; finish all mandatory calls/
finalization, complete main/source and uniform formal target steps,
explicit K, dominant slack review and final unused-code cleanup. Selected
root CurrentVerify.FreshTransactionMemory; cache disabled/two workers/8GiB
cap. Do not run full verifier/Solution root on this host.

## Current main scratch-domain port: startup and nested RLP

Reference main is now 6957805e26f4bb44ef756406a2bd14d56cf89b92. The upstream
changes are merged without rewriting published history. Fixed source,
semantics, ROM and baseline proofs match that reference exactly. No executable
change was made for this proof. Current main still claims infinity.

The new scratch/frame cursors are 2965299200/2952790016. Actual mem_init and
its reached-memory trace now derive these values. A normal downward allocator
return derives its own room and mapping of every aligned in-range cell. Old
unmapped-store/clear helpers remain conditional on pointer<=sourceBase;
that explicit premise is not available at current main startup. The unused
and now false scratch_unmapped lemma is removed.

The public Software RLP validator now reuses the general actual linked-stack
proof, including nested pushes and pops, instead of the obsolete flat-only
failure shortcut. Its complete body costs<=14*(2*length+1)+4 source ticks;
its ordinary caller costs<=14*(2*length+1)+5, with failed reads, allocations,
errors and short clocks included. Actual normal returns restore the saved
arena and retain caller locals. The memory proof now protects both sides of
the temporary interval: every word below the live frame cursor, and every
word at/above the entering scratch cursor. Existing above-cursor interfaces
are projections of this stronger proof. The actual startup specialization
therefore protects memory below 2952790016 and at/above 2965299200. It does
not claim that temporary scratch bytes are unchanged. Host input framing
also uses main's newly separated outputEnd, rather than scratchBase.

Validation: current-main-scratch-cells-v1.log PASS168jobs;
current-main-mapped-rlp-v4.log PASS1270jobs. Printed facts have only the
permitted axioms. 295 indexed modules/1427 printed facts have successful
selected-build evidence at the new reference; the total historical index
8705modules/19363facts is not revalidation of the whole proof library.
Incremental policy PASS65536entries/2488627489bytes, replacement AST reverse
closure0, fixed files unchanged relative to new main. No full verifier,
complete main source bound or finite target K is claimed. Weekly usage48%,
no reset credits, ordinary usage allowed.

Next: connect this new RLP cost and interval frame to the current item/decode
callers, replacing the old CurrentValidation flat State/Push/Memory chain and
its invalid full-memory equality. Rework witness decode/materialization,
trie-root handling, message/frame construction and actual VM entry where the
old proof relied on an unmapped scratch store. Revalidate all later caller
allowances and memory/gas contexts; the old empty-transaction/withdrawal
consequences and complete-prefix numbers do not carry over automatically.
Port target bootstrap literals/bitmap changed by main before target assembly
transport. Then resume structural table invariants, pre-state/system calls,
VM/finalization, complete source and uniform target bounds, explicit K,
dominant-slack review and final unused-code cleanup. Do not run the full
verifier or Solution root on this host. No new candidate paths were added.

## Mapped scratch runtime frames and complete current list counter

The actual nested RLP proof now retains every runtime field apart from the
temporary cursor globals, memory, locals and clock. This includes the full
FFI state/events. The public validator's real saved-mark return restores all
globals, so its checked normal frame is complete MemoryMetadata plus memory
outside [2952790016,2965299200). Temporary scratch bytes may change.

Current rlp_item_total now costs<=28*length+30 body ticks; its real normal
return derives a positive consumed size, price at that actual size, runtime
frame and outside memory. Its scoped caller retains its actual callee memory
and pays<=28*consumed+31. No canonical equality with the original entire
memory is asserted. The initialized arena transfers via runtime metadata.
The actual list counter derives each positive size and real offset/count
updates, sharing one potential of60*remainingBytes. The whole unchanged
rlp_list_count costs<=60*length body / +1 ordinary caller ticks on all outcomes.
Normal returns derive count<=length, complete runtime/outside-memory frames,
actual callee states and real continuations. No future successful parse,
allocation, mapped input or encoded-list image is an entry premise.

Cleanup removed eight unused flat-only CurrentValidation modules (490lines),
after checking their imports and preserving exact local bytes in
work/agent-notes/archive/current-flat-validation-3b28334fa.tar.gz. Their small
word lookup helper now lives in the list-counter state module which uses it.

Validation: current-rlp-runtime-frame-v1.log PASS1240jobs;
current-rlp-item-normal-v2.log PASS1255jobs;
current-rlp-list-count-cost-v1.log PASS1264jobs;
current-rlp-list-count-caller-v1.log PASS1266jobs, permitted printed axioms.
Incremental policy PASS65528entries/2488589340bytes. Inventory8737modules,
replacement AST reverse closure0, fixed files identical to reference6957805e.
322indexed modules/1503printed facts have selected-build evidence at this
reference; historical index8697/19366 is not whole-library revalidation.
Claim infinity; no complete main source bound, finite target K or full verifier
success. Weekly usage48%, no reset credits, ordinary usage allowed.

Next: reconnect encoded-item/list provenance and downstream item/decode
callers to the actual returned memory. Derive byte preservation for the
input extent below the frame cursor from its real ownership; do not assume
whole-memory equality or unchanged source bytes for arbitrary scratch-overlapping
input. Update later cost allowances and models through actual decoder/main
contexts. Witness/trie/message/frame/VM paths and changed target bootstrap
still require porting; the old main prefix and empty-input consequences remain
unrevalidated. Then complete the remaining system/VM/finalization, source and
uniform target bound, explicit K, slack review and final cleanup. No full
verifier or Solution root on this host.

## Protected byte provenance and current list-to-array conversion

Actual scratch frames now preserve byte observations below their live frame
cursor, including unaligned pointers and either endian. Generic byte-frame
lemmas live in ByteAgreementFrame rather than importing the older BlobBytes/
HostLength pipeline. The latter historical branch remains unvalidated; it is
not needed by these current parser roots.

The actual item caller derives its header encoding, paid consumed-byte bound,
complete runtime metadata, protected memory and real callee state. Each count
iteration composes these observations into an ordered list of original input
items. List provenance requires the input extent below2952790016. The actual
converter derives that separation from its existing owned-before-heap input
and heap<=2952790016 entry geometry. No future parse or encoded image is an
entry premise. Actual normal callers retain their returned memory.

The unchanged list-to-slices converter now costs<=71*length+3 body /
71*length+4 ordinary caller source ticks on every outcome. Its first pass
supplies the real ordered items/count; the actual allocation and unchecked
second pass construct the physical records. Input bytes survive both passes.
Normal returns derive the actual heap update, bounded/aligned next heap,
complete runtime metadata and preservation of every word before the entering
heap. A fresh-array-only Window over the original state is no longer asserted,
since scratch bytes also change. The shared persistent frame uses exactly the
required earlier-memory guarantee. Its real scoped caller and reached suffix
pricing are checked.

Validation: current-rlp-list-items-frame-v1.log PASS1293jobs;
current-rlp-slices-scratch-frame-v2.log PASS1321jobs, permitted printed axioms.
Inventory8737modules/replacement closure0/fixed bytes match6957805e.
376indexed modules/1631printed facts have successful selected-build evidence
at this reference; historical8697/19368 is not whole-library revalidation.
Claim infinity; no whole-main finite source bound or uniform target K/full
verifier success. Weekly usage49%, no reset credits, ordinary usage allowed.

Next: port CurrentItem's list-count branches and runtime/protected-memory
returns, then connect current header decoding and witness decoding to the
new slice caller/persistent frame and source allowances. Update every actual
consumer of the old whole-memory equality and57/58 allowances. Later witness/
trie/message/frame/VM paths, changed target bootstrap, complete source/target
composition, explicit K, slack review and final cleanup remain open. Old main
prefix numbers/empty-input consequences are not revalidated. Do not run the
full verifier or Solution root on this host.

Incremental policy PASS65528entries/2488594537bytes for this checkpoint;
no new candidate paths. This is not isolated/full verification.

## Current item/string frames and complete header-validation port

The actual item parser now costs<=60*length+10 body / +11 caller source ticks;
full RLP decoding costs<=60*length+12 body / +13 caller ticks. Their real
returned values supply positive/complete extents, runtime/protected-memory
frames and the actual callee state used by the continuation. A reusable Frame
composes these facts through real readonly prefixes and local scopes.

The actual returned kind is now recovered from each short/long list branch.
A genuine string-kind return cannot have taken either list branch. Its full
normal parse is readonly, including the real length reader. Header uint/bytes/
raw helpers derive that string kind from their own successful guard and use
this stronger frame. Their downstream word/U256/field pipeline retains its
original whole-memory preservation theorem without assuming successful string
parsing in advance. All helper allowances include failed list-kind inputs too.

The complete unchanged decode_header now costs<=251*length+473 body /
251*length+474 caller source ticks. The price tracks the actual complete decode,
slicing and field pipeline (each row decoded at most twice). Its real normal
return restores its temporary arenas, returns the actual248-byte header,
protects earlier memory, retains other globals and grows heap by<=616bytes.
Actual scoped normal/all-outcome callers are checked. Top-level parsing and
slicing use the returned memory rather than a source-memory substitution.

The complete current validate_headers now costs<=66208386 body /
66208387 caller source ticks, covering both allocations, every count/row/link
failure and actual decode/hash/link loops. The unchanged <=1024-byte rows
cost<=258496 each before their loop tick; links retain their130tick allowance.
Normal calls retain the real decoded arrays, bounded next heap and input/
workspace frames. Main's enclosing call/allowances still need reconnecting.

Validation: current-rlp-string-item-frame-v1.log PASS1280jobs;
current-rlp-decode-field-frame-v1.log PASS1292jobs;
current-header-scratch-port-v1.log PASS1412jobs;
current-header-validation-scratch-port-v1.log PASS1530jobs; permitted printed
axioms. Incremental policy PASS65528entries/2488604200bytes. Inventory8737/
replacement closure0/fixed source, semantics, ROM and proofs match6957805e.
580indexed modules/2129printed facts have successful selected-build evidence
at this reference; historical8697/19373 is not whole-library revalidation.
Claim infinity; no whole-main source bound, finite uniform target K or full
verifier success. Usage49%, no reset credits, ordinary usage allowed.

Next: reconnect current main's header-validation call and update the actual
startup/header/gas prefix allowances and retained context. Port witness
parsing consumers to the new real item/slice states and earlier-memory frame.
Replace remaining trie/materialization/message/frame/VM early-stop arguments
invalidated by mapped scratch. Finish the actual table/system/VM/finalization
connections, changed target bootstrap, uniform compiler/target transport,
explicit K, dominant-slack review and final unused-code cleanup. Historical
empty-transaction/withdrawal consequences and old whole-prefix numbers remain
unrevalidated. Do not run the full verifier or Solution root on this host.

## Main header/database prefix and actual witness pair costs

Current main's actual header caller and retained input context are reconnected
to the mapped-scratch validator. Header validation costs<=66208387 source ticks;
its real post-header gas/global prefix adds<=67. The actual run_attempt path
therefore stops within66208454ticks or reaches its first Patricia database
with the real input, payload/gas locals and lexical endpoint intact. The
existing two-database proofs are checked against the same current main: both
actual builders/callers cost<=3323240764 combined. The full run_attempt prefix
through headers, gas and both databases costs<=3389449218 before state_init,
or stops within that allowance. Genuine tables and original input images are
retained. No successful future table or state initialization is assumed.

The current host-length reader now uses Guest.outputEnd for the real host
output boundary, independently of scratchBase. This repairs its upstream
model mismatch without changing executable or fixed definitions.

The witness leaf path now costs<=60*bytes+15. The actual two-item path costs
<=bytes/4+120*bytes+35, with<=bytes/4+60*bytes+24 for its compact-call suffix.
The first item retains its real returned memory. Its runtime metadata and
outside-scratch frame preserve the physical rows below the established heap
ceiling; the compact constructor retains the real second row. The extension
suffix has a uniform2tick proof covering actual scratch allocation, all stores
and its successful suspended-frame return. Its cost proof no longer imports
the old extension/branch impossibility arguments. The syntactic leaf no-
fallthrough fact moved into the leaf module, removing that cost dependency.
The old broader zero-result and recursive early-stop consumers remain
unported and are not part of this successful witness cost root.

Validation: current-main-header-prefix-v2.log PASS2220jobs;
current-main-databases-witness-pair-v2.log PASS2620jobs, permitted printed
axioms only. Incremental policy PASS65528entries/2488606583bytes, no new
candidate paths. Inventory8737modules/replacement closure0/fixed source,
semantics, ROM and proofs match6957805e. Selected-build index now records
1457modules/4571printed facts at this reference; historical8697/19375 is not
whole-library revalidation. Claim infinity; no complete main source bound,
finite uniform target K or full verifier success. Usage49%, no reset credits,
ordinary usage allowed. Do not run the full verifier or Solution root here.

Next: reconnect state initialization and root/witness consumers beyond the
actual two-database prefix. Derive real terminal/suspended witness returns,
branch-frame stores and decoder-loop progress instead of the old zero-only
and failed-scratch arguments. Port slice/normal frames and nested callers to
real scratch-changing states; live nested cursors require the generic arena,
not an assumed original startup cursor. Later trie/materialization/message/
frame/VM/finalization paths, changed target bootstrap, complete source/target
composition, explicit K, dominant-slack review and final unused-code cleanup
remain open. Historical empty-input consequences and old534124484749whole-
prefix number are not revalidated.

## Real caught witness parsing and suffix entry

The actual decode/resolve RLP body now costs<=60*length+12, its complete caught
call<=60*length+14, and a genuine continuing return reaches the original suffix
within60*length+13 source ticks. Both outcomes retain the same real parser,
handler and callee execution; the MPT handler cannot manufacture fallthrough.

Normal parser returns and normal/all-outcome prefix traces now expose
CurrentItem.Frame, retaining full runtime metadata and protected memory
outside temporary scratch. Their actual returned memory is carried into the
suffix. Local declarations/restoration transfer that frame to the original
caller; initialized arena facts follow from metadata, not whole-memory
identity. Actual parsed values and db/p/n locals are derived from the same
caught execution. This does not assume original startup cursors inside live
nested VM frames; that later generic-arena connection remains open.

Validation: current-witness-parser-prefix-v1.log PASS1290jobs, permitted printed
axioms; incremental policy PASS65528entries/2488606570bytes, no new candidate
paths. Fixed files match6957805e and replacement closure0. Selected-build
index1461modules/4578printed facts at this reference; historical8697/19375.
Claim infinity; no complete main source bound, finite uniform target K or full
verification. Next: use these real frames in complete decode/resolve costs,
replace old zero-only/suspended-frame impossibility arguments, and connect
actual recursive witness/VM progress. Remaining task scope is unchanged.

## Real terminal/suspended decode-step returns and complete cost

The unchanged current _decode_step now has a complete all-outcome allowance
length/4+251*length+284 source ticks (<=257564 at the actual1024byte cap).
Its real converted rows, first-item protected memory, compact allocation,
second-item parser, leaf constructor, branch constructor and both scratch-
frame suffixes are included. Slice conversion contributes71*payload+4;
the selected two-item/branch suffix contributes<=payload/4+120*payload+266.
The complete post-RLP suffix is<=length/4+191*length+270. The actual caught
parser supplies its real advanced state and retained metadata to this suffix.

A normal step now derives BinaryResult: flag0 for a completed node or flag1
for a pending frame. Both extension and branch frame returns are covered.
These structural return facts need no successful future parser, allocation,
or preselected terminal path. They are derived through actual scopes, every
record store, and the real return statements. The old current_step_zero/
suffix_zero/slices_zero/after_array_zero claims and recursive no-return cuts
were removed. Their terminal-only core/frame consumers remain unported and
must use real pending-frame ownership/progress; this checkpoint does not
claim the entire decoder loop finishes in two iterations.

The now unreferenced WitnessDecodeScratch module was removed. It only held
obsolete first-store failure proofs; its exact contents are retained locally
at work/agent-notes/archive/witness-decode-scratch-before-mapped-port.lean and
in Git history. No fixed source or implementation changed. Branch-frame
allocation now has a genuine2tick all-outcome suffix; the complete persistent
branch allocation/record path costs<=231, including its successful return.

Validation: current-witness-decode-step-v1.log PASS1425jobs, permitted printed
axioms. Incremental policy PASS65527entries/2488598604bytes. Inventory8736/
replacement closure0/fixed files match6957805e. Selected index1476modules/
4618printed facts at this reference; historical8696/19388 is not full-library
revalidation. Claim infinity; no complete main source bound, uniform target K
or full verifier success. Do not run the full verifier or Solution root here.

Next: carry real pending-frame ownership, stores and progress through the
witness core. The historical generic stack-rank model already handles both
terminal/pushed cases and arbitrary witness cycles, but its old below-input
scratch layout and database invariants need porting. Current parser wrappers
still use the initialized ArenaState; nested parsing needs a generic live
cursor/limit arena. Resolve/table frames, later main/VM/finalization paths,
changed target bootstrap, complete source/target transport, explicit K,
dominant-slack review and final unused-code cleanup remain open.

## Live parser cursors and mapped witness-frame progress

LiveArena now packages the real runtime/code and existential cursor/limit
inside the current scratch region, without an original startup cursor, empty
stack or future allocation-room premise. Startup supplies this invariant;
actual readonly/metadata frames transfer it. The public validator restores
the real saved cursor and derives its own mapped nested-stack arena. Its
metadata/frame proof uses that actual cursor, not a fixed initialization word.

Current item/item-total/list-count/full-decode costs and normal frames now
accept LiveArena. Tight item60*n+10 and complete-decode60*n+12 body bounds
are retained. New body/ordinary scoped traces protect both earlier persistent
input and every existing record above the actual entering cursor, with the
real returned state/value, caller clock and continuation. The precise upper
frame reuses the generic actual-item/decode normal proof, revalidated against
the same Software source; its older looser cost is not used for the tight
current allowance. Slicing's body cost accepts LiveArena, while its normal
allocation API still returns the startup-specific arena and needs a later
live wrapper. No live arena is coerced back into the original cursor values.

Existing header-field callers explicitly transfer their initialized arena
into the live parser entry. Full current header/database-prefix and witness-
single-step integrations pass after this API extension. Their checked bounds
remain3389449218 to state_init and n/4+251*n+284 for _decode_step. This does
not yet supply a generic live-cursor complete witness-step/loop theorem.

Actual extension/branch record helpers now use the Software function literal.
Their real88byte allocation/stores derive the exact pending result, new
cursor, stored fields and allowance decrease. A new outside frame protects
both earlier input/heap and older pending records, retaining runtime fields.
A normal record call retains LiveArena and decreases the actual whole-record
allowance by at least one. Actual cursor globals derive region bounds and
at most142149 remaining records, without an extra caller range premise.
The existing stack-rank model gives initial potential<=6823154 for any live
entry with an empty stack. This is the initial potential and allocation step;
all real loop transitions/invariants still have to be connected before it is
a complete materializer bound. The core itself contains no scratch-release
call; actual parser/helper cursor preservation is part of the remaining proof.

Validation: current-live-parser-arena-v1.log PASS672jobs;
current-live-item-decode-v2.log PASS1309jobs;
current-live-parser-record-frame-v1.log PASS1318jobs;
current-live-parser-main-integration-v2.log PASS2672jobs;
current-live-witness-record-v4.log PASS1226jobs;
current-live-witness-rank-v1.log PASS1265jobs. Printed axioms permitted.
Incremental policy PASS65527entries/2488615933bytes, no new candidate paths.
Inventory8736/replacement closure0/fixed files match6957805e. Selected index
1520modules/4765printed facts at this reference; historical8696/19402 is not
whole-library validation. Usage50%, no reset credits, ordinary usage allowed.
Claim infinity; no complete main source bound, finite uniform target K or
full verifier success. Do not run the full verifier or Solution root here.

Next: extend actual slice/compact/witness suffix normal APIs to LiveArena;
connect pending-record descriptions and physical protection to decode-mode
pushes, resolve-mode reads/lookup, branch advancement and pops. Port the old
stack invariant's below-input scratch geometry to the current above-heap
region and current Patricia database images. Then use real phase transitions
to decrease the rank on every continuing iteration. Later main/VM paths,
changed target bootstrap, uniform transport, explicit K, dominant-slack
review and final unused-code cleanup remain required.

## Live slice/compact stages and normal decoder return frames

The complete current _decode_step cost now accepts LiveArena, including live
list conversion, compact-path decoding and the caught parse prefix. Its bound
remains n/4+251*n+284 (<=257564 at n<=1024). No original scratch cursor or empty
pending stack is an entry condition. Actual p+n<=heap and n<=1024 are still
needed for this node-decoding stage and must come from its actual caller.

Actual list counting now exposes protection above every separately named
cursor consistent with its real globals. List conversion composes that frame
with its actual fresh-array writes, protecting both earlier heap/input words
and older records above the live cursor. Its normal body and caller return
LiveArena, exact ordered records/count, heap update, complete runtime metadata,
both memory guarantees and real continuation. The existing persistent frame
also works at live entries. Header startup compatibility is derived from the
real heap-only global update and its original input arena; LiveArena alone
never implies the original cursor values. Header/data prefix integration
still passes with3389449218source ticks to state_init.

Compact-path snapshots now retain LiveArena from their own heap update and
unchanged cursor globals, removing their unused current-constructor-arena
import. Their real caller and persistent frame are checked at live entries.
The leaf path now carries the real itemPost and exact bodyRun. Its own guard
forces string kind zero before the actual leaf constructor; only then is the
string parser's full readonly frame applied. No clock-only replacement for
returned memory is used. The genuine64byte leaf allocation, parent stores,
bounded room and full outside-node memory frame are derived from that same
normal call. This covers older records as well as earlier input.

A new LiveFrame models decoder/allocation stages in the current above-heap
scratch layout: bounded advancing heap, nonincreasing scratch, actual live
arena, complete nonglobal runtime, retained nonheap/nonscratch globals, and
both earlier-memory/upper-record protection. Actual parser and persistent
frames construct it; composition and lexical restoration are checked. Real
leaf-body returns and both pending-record allocations now supply this shared
frame. It is not asserted for arbitrary core return-mode mutations: those
legitimately update older parent nodes/records and need phase-specific stack
views/write frames. The old NormalFrame's between-cursor-and-heap band is
historical and is not the required current-layout protection.

Actual extension/branch normal models are revalidated, deriving their real
initialized record/next cursor/allowance decrease, not a terminal-only result.
The branch model uses the standalone nullary environment and no longer pulls
in irrelevant MainEntry/SlicesNormal proofs. The generic DecodeGlobals branch
has not been revalidated; it is not a dependency of these normal models.
Broader old current_pair_frame/current_slices_frame/current_step_frame/core
terminal-only consumers remain unported and are not covered by this check.

Validation: current-live-slices-compact-step-v2.log PASS1456jobs;
current-live-slices-main-integration-v1.log PASS2641jobs;
current-live-witness-leaf-frame-v2.log PASS1365jobs;
current-witness-live-return-frame-v2.log PASS1373jobs;
current-witness-pending-normal-v2.log PASS1262jobs. Printed axioms permitted.
Incremental policy PASS65527entries/2488635764bytes, no new candidate paths.
Inventory8736/replacement closure0/fixed files match6957805e. Selected index
1532modules/4796printed facts at this reference; historical8696/19411 is not
whole-library validation. Usage50%, no reset credits, ordinary usage allowed.
Claim infinity; no complete main source bound, finite uniform target K or full
verifier success. Do not run the full verifier or Solution root here.

Next: replace the terminal-only pair/list/step normal models with genuine
terminal/pending alternatives, carrying returned row/payload ownership and
LiveFrame through the exact slice/compact/parser states. Port record views
and the stack invariant from historical low scratch/2713M constants to the
current2952M--2965M scratch region and real input/database frontiers. Resolve
normal/read-only table lookup and return-mode writes then need their actual
current Patricia images and phase-specific invariants. Derive separation
for each real caller; do not assume a before-heap input for possible scratch
buffers without checking the code. Finish the real rank-decreasing loop,
later main/VM/finalization paths, changed target bootstrap, full transport,
explicit K, dominant-slack review and final unused-code cleanup.


## Current mapped record views and writes — 2026-10-31

Actual pending-record views now describe the current scratch band:
record start>=2952790016 and record end<=2965299200. Persistent row arrays
and payloads end<=2952790016, and their floors use the ordinary source base
2701131776. The explicit upper bounds are necessary: the historical
scratch-below-persistent ordering no longer proves separation. Both genuine
extension and branch normal executions derive these new physical views,
initialized cells, preserved rows/payload ownership, real scratch allowance
decrease and LiveFrame. Parent input bounds/separation remain genuine caller
obligations, not future-success premises.

The generic node constructor now derives room for its exact requested size
from its actual normal allocation, retaining the weaker incoming-heap bound
as a compatibility theorem. The real branch decoder consequently derives
heap+176<=2952790016, its bounded aligned next heap and preserved kind3 tag;
ordinary arena room alone does not justify the persistent cap. Real branch
value words remain zero after scratch stores in the current layout.

The PREV, HASH, branch counter and branch child write proofs now use the
actual opposite separation. Their returned views retain both physical
bounds. A new View.live_frame preserves an older record above the entering
cursor and its persistent rows/payload below the entering heap across a
real decoder LiveFrame. This is for allocation/decoder stages; arbitrary
core return-mode mutations still need their phase-specific views/frames.
The older generic leaf allocation now uses the checked arena-to-persistent
constructor interface rather than the obsolete constructor argument list.

Validation: current-witness-record-views-v4.log PASS1365jobs;
current-record-views-integration-v1.log PASS2669jobs, including the real
main state-entry prefix, current leaf/value frame, normal-result transport
and older-record live frame. Printed axioms permitted. Incremental policy
PASS65527entries/2488647953bytes, no new candidate paths. Inventory8736,
replacement closure0, fixed files match6957805e. Selected index1555modules/
4892printed facts at this reference; historical8696/19418 is not whole-library
validation. Usage50%, no reset credits, ordinary usage allowed.
Claim infinity; no global finite target K or full verifier success.

Next: connect the actual pair/list/step normal paths to these returned
views and LiveFrame, replacing terminal-only contracts. The rich leaf view
still has historical2713M floors; port its actual compact/value proof before
using it at general current entries. Carry the actual slice/parser states,
not clock-only replacements. Then port full stack/resolve/return phases and
prove the real rank-decreasing loop; continue the main/VM/finalization and
uniform target transport, explicit K, dominant-slack review and cleanup.
Do not run the full verifier or Solution root on this host.


## Complete current decoder normal results — 2026-10-31

The actual unchanged _decode_step now has a checked whole normal-return
contract, current_step_frame: LiveFrame source/post plus the physical
NormalResult for empty, leaf or pending extension/branch. Real persistent
heap advancement, preserved earlier words/older records, exact original
scope restorations and actual record allowance decrease are included.
This is a helper contract with explicit real-entry obligations: live named
scratch cursors, bounded aligned heap, input<=1024bytes in the ordinary
region before the actual database and db<=heap. Its callers still must
establish these from their executions. It is not a whole materializer/main
or formal target-step bound.

The path/value row parsers now carry their actual callee post-states and
body runs. Their own real string guards force kind0; only then is full
readonly state equality used to preserve rows below scratch. The rich leaf
view now uses the actual sourceBase2701131776 floor. Actual compact return
snapshots retain bounded heap, physical named scratch, LiveFrame, real rows
and both saved scopes. The same pair execution returns the real leaf or
initialized pending extension, with the same actual path/value bytes.

The old current_pair_frame/current_slices_frame/current_step_frame
terminal-only proofs are replaced. The pair model distinguishes its current
heap from the already allocated array frontier. Actual list conversion
returns either the pair result or the seventeen-row branch result, including
real initial empty branch values, fresh payload/rows and reduced scratch
allowance. Whole decoding composes these with the real caught parser frame.
That prefix now exposes protection above every named cursor consistent with
its actual globals; the fixed whole-scratch outside frame alone would not
protect older records below the original scratch top.

Cleanup removed obsolete compact/extension no-return branches and duplicate
terminal-only pair logic. Pure item result-injectivity/field facts moved to
ItemValueSyntax; their names stay available without loading call-frame
proofs. Control uses SlicesSyntax directly. DecodeGlobals now unfolds the
actual Guest.Software.guestFn_rlp_item, and its generic globals/call/frame
interfaces replay successfully. No extra candidate paths were added.

Validation: current-witness-full-normal-v3.log PASS2729jobs, including the
complete current decoder normal contract, actual main state-entry prefix
(still3389449218source ticks) and generic item frame trace. Earlier staged
checks passed1435/1450/1497jobs; failed intermediate logs were not indexed.
Printed axioms permitted. Incremental policy PASS65527entries/2488650367bytes;
inventory8736/replacement closure0/fixed files match6957805e. Selected index
1573modules/4935printed facts at this reference; historical8696/19421 is not
whole-library validation. Usage51%, no reset credits, ordinary usage allowed.
Claim infinity; no complete main source bound, finite uniform target K or
full verifier success. Do not run the full verifier or Solution root here.

Next: connect the real core decode/push branch and physical older-stack
preservation to this returned model; port stronger nibble-byte results where
needed. The historical stack model's ordering of records already matches
successive downward allocations, but its HashValid/input floors and
between-cursor-and-heap frame consumers remain historical. Use the checked
record View.live_frame for decoder stages; return-mode parent mutations need
their own phase-specific views/write frames. Port real resolve/current
Patricia lookup, return/cache/branch phases, then prove the full ranked loop.
Continue actual main/VM/nonempty paths/finalization, changed target bootstrap,
uniform target transport, explicit K, slack review and unused-code cleanup.


## Current decode-mode stack and strict rank — 2026-10-31

The actual unchanged core decode-mode normal iteration now connects the
current whole _decode_step contract to its physical stack and strict rank.
The real scoped call returns a terminal empty/leaf or pending initialized
record. Its original terminal/push tail executes actual stores, stage reads
and local assignments; its d scope restores exactly. A terminal result
preserves older activations and changes decode to returning. A pending
result installs the real PREV link, fresh top/slot/mode, preserves the older
stack, spends actual scratch allowance and changes decode to resolve with
a strict rank decrease. db/go and all four data-word locals are retained.
No input hash ordering or acyclicity premise is introduced.

CoreDecodeCallNormal/CoreDecodeResumeNormal/CoreDecodeNormal now use the
actual current decoder and LiveFrame directly. Their old RootBoundary/input
and below-unmapped-scratch dependencies are removed. Real caller obligations
remain explicit: heap arena/alignment/cap, live named scratch, bounded
parent slice before the actual db and db<=heap. Core decode/push results
are derived from the same genuine normal run, not assumed future outcomes.

The physical record regions frame and whole-stack frame now protect
persistent data below the entering heap and older records above the entering
cursor separately. The old single between-cursor-and-heap interval is
replaced. Actual pending HASH and PREV words, record cells, row arrays and
owned payloads all survive. Both normal and stronger nibble-result push
lemmas now use the live two-sided frame. Stack HashValid and selected-row
bounds use actual sourceBase2701131776 rather than the old2713M floor.
LiveFrame exposes retained runtime fields and a store_between lemma: real
PREV stores must be above the persistent frontier and below the old cursor.
The actual record/cap facts discharge both inequalities.

The cache-view helper now requires the actual nonnull child's32byte header
end<=persistent cap as well as older payloads before that child. Its real
HASH24 store protects the older persistent data and above-heap records via
the regions frame. This condition must come from the actual returned node
and bounded current heap when return mode is connected; ordinary mapped
arena ownership alone does not establish the persistent cap.

CurrentWitnessCoreDecode's obsolete terminal-only mode0/empty-top normal
claim is removed. The existing full physical stack theorem replaces it.
Its all-outcome decode caller allowance is now n/4+251*n+285 (<=257565 at1024),
including actual pending pushes and failed reads/stores. Both tails spend
zero source call/loop ticks because they are straight-line; their target
instructions still need the final transport accounting. Historical
CurrentWitnessCoreLoop/Frame/Cost two-iteration/200223 claims remain unported
and must not be used for current main.

Validation: current-witness-live-stack-push-v2.log PASS1373jobs;
current-witness-core-decode-stack-v2.log PASS1533jobs;
current-witness-decode-mode-integration-v1.log PASS2745jobs, including actual
current decode-mode stack/rank, both push contracts, all-outcome caller
cost and unchanged3389449218source-tick main state-entry prefix. Printed
axioms permitted. Incremental policy PASS65527entries/2488648872bytes;
inventory8736/replacement closure0/fixed files match6957805e. Selected index
1594modules/5010printed facts at this reference; historical8696/19428 is not
whole-library validation. Usage51%, no reset credits, ordinary usage allowed.
No new candidate paths. Claim infinity; no finite global target K or full
verifier success. Do not run full verification or the Solution root here.

Next: carry actual compact nibble bytes where needed by the existing strong
path invariant, and connect real resolve mode/current Patricia database
lookup and return/cache/branch phases. Each phase needs its own physical
write frame and rank transition; arbitrary parent mutations cannot use the
decoder's earlier-word preservation. Only then compose the complete ranked
loop. Preserve actual main/VM/nonempty/finalization scope, changed target
bootstrap, full target transport, explicit K, slack review and final unused
proof/implementation cleanup. Remove or replace the remaining two-iteration
shortcuts once their real caller dependencies are ported.


## Current Patricia resolver helper — 2026-10-31

The complete unchanged _resolve_step now has checked all-outcome source
cost60*n+281 (<=61721 at1024) and its actual normal-return classification:
empty, genuine allocated hashed node, or bounded next input slice with a
real pending hash span. Lookup is the current fixed-depth Patricia getter,
not the old hash-table probing model. Its whole scoped lookup costs<=265;
the resolver suffix including missing-preimage constructor costs<=268.
Query alignment/readability, lookup success and future allocation success
are not supplied premises. This is still source call/loop accounting, not
a global formal target K.

A new CurrentTable.NodeLookup.Database bundles the actual Patricia value
image, decoded physical rows, <=1024byte lengths and sourceBase/before-table
input bounds. It has local-state and protected-earlier-heap transports;
actual normal lookup membership derives real bounded ordinary input spans.
Main's HasTables.node_database now constructs this bundle from its real
completed node builder and retained witness rows, even after the code
builder has run, with the actual table end before the current heap.
The database trace/HasTables now retain boundary<=nodeUpper/codeUpper facts
already derived by their actual callers; StateInputs is adjusted accordingly.
No new separation assumption is added to main's execution.

Resolver syntax unfolds the actual Guest.Software program and uses current
NodeLookup's three-word ABI. Pure lookupValue replaces obsolete hash-table
output imports. The normal lookup/suffix proofs use the real scoped current
getter's returned row membership and readonly state; missing preimages run
the actual hashed-node constructor. Its exact32byte persistent room and
bounded next heap are derived from the same real normal allocation. Ordinary
mapped arena room alone is never used to prove the persistent cap.

The whole normal resolver carries its actual caught parser state/above-live-
cursor frame, protected database, restored named scratch, and LiveFrame.
It preserves earlier persistent data and older records above the entering
cursor, while genuinely advancing heap on the hashed-node case. Real result
tags/cache words and pending32byte input spans refer to the same final state.
ResolveResult now retains the hashed node's persistent extent and bounded
final heap, plus a current scratch store_above lemma; the prior conditional
store_below lemma remains valid but is not the current HASH-store geometry.
The old RootBoundary and unmapped-scratch dependencies are removed from
both whole resolver helper proofs. Actual entry database/heap/input facts
remain explicit caller obligations.

Validation: current-resolver-helper-integration-v1.log PASS2779jobs, including
whole current resolver cost/normal result, main StateInputs/database bundle,
and the previously checked actual decode-mode stack/rank. Staged checks
passed2640/1421/1475/2668jobs. Printed axioms permitted. Incremental policy
PASS65527entries/2488661004bytes; inventory8736/replacement closure0/fixed files
match6957805e. Selected index1632modules/5085printed facts at this reference;
historical8696/19435 is not whole-library validation. Usage51%, no reset
credits, ordinary usage allowed. No new candidate paths. Claim infinity;
no complete materializer loop/main source bound, finite uniform target K,
or full verifier success. Do not run full verification or Solution here.

Next: connect the current core resolver scoped call, real head HASH store,
mode/input updates and strict stack rank transition. The helper LiveFrame
ends before that existing-record mutation; use a phase-specific stack frame
for the HASH store, preserving rows/payloads below persistent cap and older
records by address order. Then connect return/cache/branch phases, stronger
nibble-byte views where needed, complete ranked loop, real main/VM/nonempty/
finalization, target bootstrap/transport, explicit K and final cleanup.


## 2026-10-31 — Current core resolve mode and bounded stack outputs

Connected the actual current core resolver call and both real return shapes
through the head HASH store, top/input/mode updates and scope restoration.
The inputs use the actual Patricia Database derived by main, its table end
before the entering heap, and the physical record/stack/live-scratch facts.
There is no old RootBoundary, hash-map model or below-sourceBase scratch
premise in this current path. The complete resolve mode costs at most61722
source call/loop ticks at a <=1024byte record input.

The helper LiveFrame ends before the existing head HASH mutation. Its real
store is above the persistent cap; the stack proof preserves earlier rows,
payloads and older records using persistent bounds and record address order.
Both actual resolver outcomes retain the physical stack and strictly decrease
rank. ResolveStep and DecodeStep now also retain a next heap <=2952790016
and LiveArena post; these are established from real returns and allocations,
not supplied future-success assumptions. The resolved phase returns the
actual preserved Patricia Database and a full before-entering-heap frame.
DatabaseFrame's earlier memory statement now covers every address below the
incoming heap, instead of the obsolete reversed scratch/payload band.

Replaced obsolete CoreResolveViewFrame contents with current Patricia frame
adapters. Existing old consumers outside these selected roots remain pending
port/cleanup. No program or fixed-source bytes changed; no new candidate paths.

Validation: current-core-decode-resolve-integration-v1.log PASS2789jobs,
including actual core resolve stack/rank, its source cost, full core decode
stack/rank and main StateInputs. Earlier normal/stack stages PASS1557/1685jobs.
Printed axioms permitted. Incremental policy PASS65527entries/2488663733bytes;
inventory8736modules/replacement closure0/fixed files match6957805e. Selected
index1641modules/5112printed facts at this reference; historical8696/19438 is
not whole-library validation. Account usage52%, no reset credits, ordinary
usage allowed. Claim infinity; no complete materializer loop/main source
bound, global finite target K or full verifier success.

Next: actual return/cache/extension/branch/pop phases and their phase-specific
memory/database frames, then assemble the current ranked materializer loop.
Return writes can update earlier persistent parents, so a decoder-style full
before-entering-heap frame cannot be asserted for that phase. Strong nibble
views, remaining main/VM/nonempty/finalization, target bootstrap/transport,
explicit K, slack review and final cleanup remain open.


## 2026-10-31 — Current return cache, extension pop and next-child stack

Ported the real return child-cache stack proof to current above-persistent
scratch. Its incoming heap cap now supplies the returned node's persistent
extent; record/HASH separation uses the actual scratch lower bound. Added
cache_memory_before and cache_database: the real HASH24 store preserves the
actual Patricia database below the returned node's allocation frontier.
This does not assert a false whole-before-current-heap frame for return mode.

The real parent metadata stores now use nodePersistent (node+size<=persistent
cap), instead of the obsolete large-node lower bound. The exact original
extension constructor derives its own56byte room from normal allocation;
its actual caller retains room and all scope restorations. The extension
frame now protects both earlier persistent memory and older scratch records,
returns bounded next heap and live scratch, and exposes the full current
LiveFrame. The complete extension stack pop derives its owned fresh result,
physical tail stack, actual returned extension fields and strict rank drop.
Current sourceBase replaces the old2713731432 result/extension floor.

The tail-stack frame protects the two separate physical regions, rather
than the obsolete band between record and payload. The actual continuing
branch child/counter/index stores now supply this frame, preserving older
records/rows and the head PREV/HASH while the real next slot/mode and updated
counter prove a strict returning-to-resolve rank decrease. No future-success
or input acyclicity premise was added. Nine existing proof modules changed;
fixed program/source bytes remain unchanged and there are no new paths.

Validation: current-return-foundations-integration-v1.log PASS2742jobs,
including cache/database, complete extension pop, next-child physical stack,
current whole resolver stack/cost and main StateInputs. Earlier extension
and continuing-branch checks PASS1530/1262jobs. All printed axioms permitted.
Incremental policy PASS65527entries/2488666459bytes; inventory8736modules,
replacement closure0, fixed files match6957805e. Selected index1656modules/
5157printed facts at this reference; historical8696/19440 is not a validation
of the whole library. Usage52%, zero reset credits, ordinary usage allowed.
Claim infinity; no complete current ranked materializer loop, full main source
bound, global target K or full verifier success.

Next: port the real final-child value parser, branch metadata/pop and their
precise persistent-prefix/above-record frame; reconnect stage dispatch and
whole return mode. Its parser must use current LiveArena and both actual
memory regions, without the old scratch<=2713717616 premise. Cache now needs
the actual heap cap; extension callers consume room and bounded/live outputs.
Older unported return/rich-loop consumers are not covered by these checks.
Then complete ranked loop, rich nibble views as needed, remaining main/VM/
nonempty/finalization, target bootstrap/transport, explicit K and cleanup.
