# Status — update this section frequently

**Objective corrected by the user on 2026-10-17:** obtain a reasonably tight finite runtime bound for the **CURRENT, UNCHANGED Pancake implementation on `main`**. There is **no required numerical ceiling**. In particular, exceeding Yukon's score limit is not a failure and does not authorize replacing an algorithm.

**Pinned reference:** local `main` is `7d656e5b6878aa420de793d9d6f689fa26ec0842`. `Guest/Ast.lean`, `Guest/guest.pp.pnk`, `submission/Solution.lean` and `submission/claim.json` currently have no changes relative to `main`. Do not change the program, its data structures, compiled ROM or semantics to improve the bound.

**The goal is NOT complete.** No whole-program finite bound has been proved. The submission still claims infinity. The earlier 45% estimate concerned the previous, misdirected plan and must not be reused as a progress estimate for this corrected task.

**Plan correction:** stop radix replacement, cross-program equivalence and candidate compilation work. Retain existing work until its dependencies have been reviewed, then remove unneeded code under the cleanup item below; Git retains its history. Reuse checked theorems that apply to the unchanged program: input parsing, hashing, allocation, original hash-table construction/lookup, gas accounting and quantitative compiler/boot results. Judge applicability from theorem statements; some original-program helpers live under `WitnessRadix/` and are still useful. Replacement-only results are historical reference, not remaining obligations.

**Original-table budget:** the previously proposed witness-construction allowance of 21,004,777,811,675,496 is a conditional partial upper bound, not a whole-program result or a lower bound. Its exceeding Yukon's score cap is irrelevant to the corrected objective. Resume accounting for the original tables, improving dominant slack where justified and retaining explicit conservative terms where needed.

**Current authorization:** continue autonomously toward the corrected goal. The user's earlier no-stop-point instruction remains in effect. Local/offline, memory/disk, permitted-axiom and full-verifier restrictions remain in force. Do not silently reintroduce a score threshold or an implementation change as a prerequisite.

## Current plan — authoritative

- [x] Correct the objective and pin the unchanged reference above; retire the numerical score gate and replacement route.
- [x] Inventory applicable proofs for the original implementation and list the remaining whole-program obligations. [Inventory](work/agent-notes/original-plan-inventory.json) identifies original entry points, remaining global obligations, baseline identity and import isolation. Counts are not completion metrics.
- [x] Clean up unneeded branch-added code after the dependency inventory: remove the replacement Pancake implementation, replacement-only equivalence proofs, and associated generators, test harnesses and candidate artifacts. Retain or extract shared helpers required by proofs of the unchanged implementation; decide from actual dependencies, not directory names. Update imports, build metadata and evidence indexes, then check the retained proof dependency closure and confirm the baseline program/artifacts are unchanged. This cleanup is authorized and must be completed as part of the task.
- [ ] Bound the original witness construction and later queries, including collision chains, duplicate multiplicities, both insertion scans, growth and actual hashing/copying costs. Retain the original implementation even if the resulting number is large.
- [ ] Close the original program's global accounting: decoded input and headers, gas/charge/refund and child-call behavior, mutable state/journal/rollback, heap and trie/query progress, output, and covered failure/unwind paths. Derive entry and affordability premises at every use.
- [ ] Assemble an explicit phase-by-phase bound under the existing documented input/gas/outcome scope. State accounting units precisely; Pancake evaluator clocks alone can omit real work. Where reporting target instructions, use the existing baseline compilation of the unchanged source.
- [ ] Evaluate the resulting expression exactly and reduce unjustified or dominant slack. No K cutoff applies. Distinguish proved bounds, conditional bounds and measurements.
- [ ] Final cleanup sweep before final validation: remove remaining unneeded scaffolding/proof branches and refresh retained dependency/evidence checks; preserve the pinned baseline.
- [ ] Complete the applicable quantitative proof/transport for the unchanged baseline and validate with targeted resource-limited checks. Produce the finite bound, its assumptions and evidence. Yukon submission or a score-compatible claim is not a completion requirement; do not alter claim.json merely to fit its numeric format.

**Cleanup completed:** removed the replacement source/generator/harness/artifacts and 258 replacement-only/unreferenced Solver modules. Shared definitions and original portions of mixed files were retained/extracted. The [cleanup manifest](work/agent-notes/original-plan-cleanup.json) records scope; all 601 affected retained/new modules were checked through 22 leaf targets in original-affected-closure-v3.log (1618 jobs, successful, permitted axioms). Baseline source, semantics, ROM and fixed proofs remain unchanged. Incremental policy passes at 61,306 entries/2,252,644,684 bytes; this is not full verification.

**New checked original-program bounds:** the entire original constructor body has a summed source-clock budget. For N decoded records inside B encoded bytes, its arithmetic allowance is at most `215*N + 7*triangle(N) + 20*((B-4*N)/136) + 46`, with `2*triangle(N)=N*(N-1)`. Entry/code/arena/clock premises remain explicit. The actual decoder Records prove payload-byte sum + 4*N <= B. Actual original dictionary lookup costs at most `6*D+3` source clocks for D distinct observed keys, including arbitrary duplicates and query alignments. These are intermediate source-clock facts, NOT a target runtime K or a whole-program theorem. Empty constructor callers still use their separate actual zero-record contract.

**New checked root/caller facts:** actual normal `validate_transaction` execution and its full, unchanged caller continuation derive a three-word intrinsic result with regular and floor components at most 16,777,216. The cap survives every intervening call and the conditional blob-fee branch. The actual gas split then initializes liquid/reservoir words with `liquid + intrinsicRegular <= 16,777,216`; scalar gas reads and the available call clock follow from normal execution. Successful closure: original-root-caller-normal-v1.log, 1094 jobs, permitted axioms. This does not price preprocessing or establish a whole-program gas ledger.

**New checked frame-allocation facts:** both actual arena allocators derive their unsigned guards from aligned natural room, update the correct cursor, and preserve all memory/FFI cells. The original `frame_new` prefix (two marks, 280-byte allocation, full clear) executes in exactly 15 source clocks under explicit code/cursor/room/domain/clock premises. Every frame word is zero at that point, including liquid/used/spill; words outside its own allocation are preserved. Successful combined closure: frame-new-zero-v3.log, 1102 jobs, permitted axioms. Incoming message gas, later frame stores/helper frames, arena reachability and global accounting remain open.

**New checked physical frame prefix:** the clear, two further arena allocations, three stack metadata stores and seven message/frame stores now compose in the actual `frame_new` AST through the entry to `compute_jumpdests`. Both zero regular counters are derived from the actual clear; the resulting regular ledger equals incoming `MSG_GAS`, with exactly 17 source clocks for this prefix. Code/cursor/alignment/arena room/mapped memory/message separation/clock premises remain explicit. The later bitmap/log/delete helpers and caller message construction still need their own frames/reachability. Successful combined closure: frame-new-fresh-v2.log, 1107 jobs, permitted axioms. This is not a whole-frame return theorem or a target runtime bound.

**New checked bytecode-helper contract:** the entire unchanged `compute_jumpdests` body and actual scoped call now check, including allocation, clear, all PUSH/continuation-byte cases, optional bitmap stores, strict PC progress, loop, return and scopes. Code bytes may be arbitrary; mapped regions and code/cursor/room/clock entry facts remain explicit. It preserves all memory at/above the incoming scratch cursor. Caller source-clock allowance is `n + memzero_price(bitmap_bytes(n)) + 3`, with `bitmap_bytes(n)=8*((n+63)/64)+8`. Conditional bounds are 131,588 for n<=131,072 and 65,796 for n<=65,536; actual caller length bounds still need reachability. These omit straight-line work from source clocks and are NOT target runtime K. Successful retained closure: jumpdest-retained-v1.log, 1120 jobs, permitted axioms. Removed the unused preliminary abstract opcode model; retained the selector connected to actual branch execution.

**New checked constructor helpers:** the unchanged log-list caller consumes 3 source clocks and the actual `(20,4)` delete-table caller consumes 12, including all six allocations and the short clear. Both derive actual arena guards and preserve memory below the lower arena cursor and at/above the incoming scratch cursor. The jump-destination helper now has the same two-sided memory frame. Actual htab_count declaration/assignment calls consume one clock each and preserve memory. Global-valued final frame stores are supported without substituting literals for runtime expressions. Successful combined closure: scratch-helpers-count-v1.log, 1110 jobs, exit 0, permitted axioms. These remain intermediate source facts, not a whole-frame return or target runtime bound.

**New checked whole-frame constructor:** the entire unchanged frame_new body and its real scoped caller now execute under original-entry code, mapped/protected message/count cells, arena alignment/room and clock premises. All helpers and stores are derived; the complete fresh frame's regular ledger equals incoming MSG_GAS at return. A mapped live arena derives every helper mapping premise. Exact reserved room is bitmap_bytes(n)+2656 bytes; caller source-clock allowance is n+memzero_price(bitmap_bytes(n))+38 (conditional literals131623 at n<=131072,65831 at n<=65536). Those length and entry premises still require actual caller reachability. Successful combined closure: frame-new-call-v1.log1154jobs, exit0, permitted axioms. This is NOT a whole-program runtime/target bound. Caller message initialization, all-outcome global accounting and target transport remain open.

**New checked physical root gas stores:** normal execution of the actual validator/caller now reaches and executes both TE_GAS and MSG_GAS with the original capped mgas. At each store, the physical word plus the validated intrinsic regular component is at most16,777,216. Helper returns, base pointers, destination mappings and all intervening local transport are derived from normal execution, including the access-list loops and optional blob/setcode branches. This does not price those prefixes or prove that later mutable-map/message-processing calls preserve the stored gas. The whole frame constructor additionally preserves all memory outside the incoming live arena, including parent frames. Successful combined closure: root-msg-normal-v2.log1161jobs, exit0, permitted axioms. Whole runtime/global/target obligations remain open.

**New checked active-frame initialization:** the unchanged frame_open body and actual scoped caller compose frame_new with the real104-byte continuation allocation/clear, all four record stores (including MSG at offset40), global activation and return. Both child ledger and every word outside the incoming live arena are preserved as required; the activated child's regular ledger equals MSG_GAS. Exact reserved room is bitmap_bytes(n)+2760; caller allowance is n+memzero_price(bitmap_bytes(n))+45 source clocks. Original entry/code/ownership/clock premises remain explicit; this does not connect through all message preprocessing or establish global gas/runtime. Successful combined closure: frame-open-call-v1.log1168jobs, exit0, permitted axioms.

**New checked persistent records:** both original te_new (200bytes) and msg_new (176bytes) bodies/callers derive real alloc and clear executions, initialize every word to zero, reserve exactly their sizes for aligned incoming heap cursors and preserve every outside word. Each actual caller consumes10source clocks. Entry code/heap/room/domain/clock premises remain explicit. Successful fresh-record-call-v1.log1065jobs, exit0, permitted axioms. Actual warm-map preprocessing and cross-callee message ownership remain open.

**New checked account/storage key helpers:** the actual htab_hash20/52-byte aligned and unaligned bodies and callers now execute with exact results and unchanged memory/FFI; both unrolled sizes cost one caller source clock. Actual aligned memeq20/52-byte bodies/callers execute every word/tail-byte comparison and early return, also one caller source clock. Input/code/clock/read premises remain explicit. No uniform byte-loop fallback,60-byte hash, mutable-map growth/deletion/ownership or global query aggregate is claimed yet. Successful hash-sized-call-v1.log1194jobs and memeq-sized-call-v1.log1092jobs, exit0, permitted axioms. Source clocks omit straight-line work and are not target K.

**Immediate next work:** prove later message/map preprocessing memory frames and connect the capped root MSG word to the actual active frame/global regular-gas ledger, then successful-child memory frames/merges, rollback and block reservation/counter facts. Preserve the original program and account for parser/failure paths, mutable maps and trie/query progress. Transport the resulting phase counts to the unchanged baseline target; no numerical ceiling applies.


## Historical evidence and superseded plans

Everything below is evidence/history unless consistent with the current plan above. Older instructions to obtain a bound below a score cap, pass a numeric feasibility gate, build a radix replacement or complete a replacement certificate are superseded. Preserve these records for reproducibility; do not treat their checklists as active goals.

## Completed, with limits

- [x] Checked the actual three-list witness decoder suffix: all three real
  decode_bytes_list calls, pointer/count SI stores, last return and lexical
  restores. Normal execution derives all three Records, node<=1024/code<=65536
  item bounds, header count<=256, six stored fields, exact sequential array
  cursors/alignment and final cursor<=initialArray+4*witnessExtent. Earlier
  arrays/fields survive later allocations and SI stores. Source clock bound is
  deliberately loose and is not target K. Actual adjacent witness Records
  also give combined node/code count<=encodedBytes/4. Initial validated witness
  offsets, copied input, code/domain/layout/heap and arena room remain explicit;
  the prefix before this suffix and header validation/startup reachability
  still need proof. Success witness-arrays-normal-v3.log1344targets; supporting
  logs in PROGRESS. Index4668/7629, incremental policy61534entries/2253818207bytes.
  Infinity; no finite K/full verification or global feasibility result.

- [x] Derived both actual decoded constructor invocations and both dictionary
  pairs at the actual runtime entry, without assuming constructor results or
  the second entry heap. Input field geometry and actual own-memory frames
  preserve si56/64; decoded cells, fixed metadata/code, exact selected cursor,
  and remaining clocks supply the second call. Covers empty/nonempty arrays
  and preserves the earlier original/radix dictionaries across the second call.
  Successful witness-next-arguments-v1.log1501,
  witness-paired-environment-v1.log1440,witness-next-decoded-call-v1.log1556,
  witness-decoded-initialization-v2.log1557targets; permitted axioms. Initial
  decoded records, startup/hash/input structure layout/code, public agreement,
  combined arena room and clock allowances remain explicit. Frontend/header
  reachability, whole runtime and global/compiler/target finite bound remain
  open. Index4660/7614, incremental policy61525entries/2253768653bytes.
  Infinity; no full verification, finite K or final acceptance. Whole-task
  conversational estimate45%, rough35-55%; not a certificate completion metric.

- [x] Checked uniform actual dictionary caller for zero/positive counts, then
  entire decoder-backed caller: actual VarList.Records supplies raw pointer/
  length reads, array arena/alignment, per-item hash arenas, raw/aligned public
  buffer ownership and max-item sizes. Null actual array pointer0 is accepted
  only on count0, using an unused logical record base at the table. Full control/
  heap update and each own earlier-memory frame survive empty bodies/callers.
  EntryEnvironment and Records.of_safe_frame carry the second map's code/hash
  metadata and actual decoded array through the first call. Exported the actual
  selected capacity <=4*N+4 through supported bodies, callers and packaged
  result. Exact heap words, alignment/range and capacity-based upper cursor
  bounds check. Conditional two-map arena arithmetic checks at max encoded
  input size assuming frontend cursor<=arenaLower+128*encodedBytes+1MiB and
  combined decoded count<=encodedBytes/4; these premises still need execution
  reachability. Latest closures witness-cap-export-closures-v1.log1505 and
  witness-cap-export-decoded-v1.log1542targets, allowed axioms; earlier logs in
  PROGRESS. Concrete full two decoded-call entry derivation, frontend/header
  cursor reachability and whole runtime/global/compiler/target proof remain
  open. Infinity; no finite K/full verification/final acceptance.

- [x] Checked conditional composition of the actual two nested run_attempt
  constructor calls into its actual runtime suffix. DictionaryPair packages
  common observations, both physical models and read support; own frames and
  allocation ordering preserve BOTH first-map models across the second call.
  Actual nested lexical restores, both final dictionary pairs, equal locals/
  globals/FFI/public memory hold at runtime entry. ConstructorReturn derives
  code/domain/endian fields from actual evaluator invariants. Context transport
  handles the first allocation's heap update for a different second array.
  Success mutable-next-context-v1.log1332,mutable-dictionary-pair-v2.log1359,
  mutable-call-result-v2.log1437,mutable-dictionary-call-v1.log1439,
  mutable-initialization-v2.log1500targets; permitted axioms. This composition
  assumes both concrete constructor-entry contracts and allocation ordering;
  decoder/header/startup reachability and null-pointer empty API unification
  remain open. Entire runtime replacement and global/compiler/target finite
  bound remain open; infinity, no full verification or final acceptance.

- [x] Checked concrete lookup read support from completed construction graph
  through terminal completion, full loop, helper/core/scopes, helper ABI/final
  return, paired population/allocation/full body and actual constructor caller.
  Every radix lookup read belongs to allocated protected cells. Those cells
  lie from records through the actual final heap cursor; earlier fixed hash
  buffers and later allocation prove the new constructor's safe-word premises.
  New checked preservation bridges retain an earlier radix root/representation/
  read support, original full physical Built invariant and original record cells
  through the later constructor's actual own-memory frame. No equality of
  original/radix private contents is assumed. Logs radix-allocated-read-bounds-v2,
  radix-completed-support-v1,radix-terminal-supported-v1,
  radix-loop-supported-result-v1,radix-loop-supported-v1,
  radix-helper-nonempty-supported-v1,radix-helper-built-supported-v1,
  radix-helper-call-supported-v3,radix-constructor-finish-supported-v1,
  mutable-populate-supported-v1,mutable-table-supported-v1,
  mutable-execution-supported-v1,mutable-call-supported-v2.log1423targets;
  permitted axioms. Actual two-map initialization composition, decoded input/
  headers/startup reachability and entire runtime replacement still open.
  Global gas/state/Q/heap/compiler/target finite bound still open. Infinity;
  no full verification, finite K or final acceptance.

- [x] Checked decoder-to-constructor adapter: actual nonempty decoded pointer/
  length cells, ordinary record layout, each input hash arena and raw/aligned
  public buffer ownership. Earlier decoded arrays survive later allocations
  preserving their cells. Actual run_attempt initialization suffix is the two
  nested nodedb_build calls, with arguments provably loaded from si40/48 and
  si56/64. Full paired constructors/callers now additionally preserve each
  program's own safe words through every record/hash/update, helper, allocation
  and scope; the earlier private dictionaries may differ between programs.
  Safe-word premises are concrete protection from hash buffers and new private
  allocation, not assumed memory preservation. Successful
  mutable-decoded-data-v3.log1439,input-records-frame-v2.log1300,
  mutable-run-attempt-v3.log1466,mutable-radix-step-framed-v3.log1350,
  loop-framed-v1.log1354,populate-framed-v1.log1383,table-framed-v2.log1397,
  execution-framed-v1.log1409,call-framed-v1.log1412targets; permitted axioms.
  First-map model/read-footprint preservation through the second map still
  needs geometry and invariant transport. Whole decoder/header reachability,
  entire runtime context and global/compiler/target finite bound remain open.
  Infinity; no full verification or finite K.

- [x] Checked actual paired original/radix constructor ABI, including ignored
  results and scoped assigned returns around arbitrary continuations. A common
  finite callee environment is derived from real code metadata. Added separate
  actual zero-record bodies and paired callers accepting any record pointer,
  including the empty decoder's null pointer, without record/hash assumptions.
  These preserve selected earlier memory, globals and FFI. Decoded item geometry
  now proves non-wrapping input subranges, actual pointer cells, aligned array
  geometry and per-item hash arenas; prefix-region raw/aligned hash accesses
  also check. Successful mutable-radix-call-v1.log1410,
  radix-empty-public-v2.log923, mutable-empty-v1.log1359,
  mutable-empty-radix-call-v2.log1376, input-record-geometry-v1.log1302 and
  decoded-constructor-data-v1.log1326targets, permitted axioms. Whole decoder/
  two-map initialization and runtime context replacement remain open; fixed
  buffer startup/layout, global gas/state/Q/heap/compiler/target and finite K
  still open. Claim infinity; no full verification. The conversational 40%
  estimate is uncertain and does not imply a proportion of certificate work.

- [x] Checked full paired original/radix nodedb_build bodies: both actual
  cap declarations/doubling loops choose the same capacity and pay the same
  prefix clocks; allocation/clearing, every record/hash/set/copy, radix helper,
  returns and outer scopes compose. Both return the same table pointer and
  preserve common globals/heap cursor, complete FFI histories and selected
  public words. Original Built/History/Records/KeysMatch and candidate actual
  QueryMemory tree representation refer to the same observed dictionary.
  Explicit decoded-record, code/arena/BufferRegion/nonalias/caller-state and
  clock premises remain; call ABI checked below, whole-guest reachability/context and
  global/compiler/target resource proofs still open. Successful
  mutable-radix-execution-v2.log1407targets, allowed axioms; index4606/7543,
  latest prior policy61470entries/2253400378bytes. Infinity; no finite K/full
  verification. This is a conditional source refinement, not final acceptance.

- [x] Checked actual paired original/radix witness-record iteration and
  entire record loops. Both observe identical keys and FFI histories; original
  insertion history equals radix key-prefix entries in ordinal order, including
  duplicates. Built/Records and Prefix/FixedData/Mapped invariants advance;
  chosen public memory remains equal. Original/radix source clocks bounded
  separately; no target K. Actual original/radix lookup bodies now provably
  return the same last matching slice from synchronized history and represented
  radix tree, at all query alignments. Allocation/radix-finish public frames,
  initial input ownership/layout reachability and whole-context replacement
  remain open. Logs mutable-witness-radix-loop-v1.log1354targets and
  mutable-witness-lookup-agreement-v1.log1345, allowed axioms. Index4589/7518,
  policy61454/2253325560bytes. Infinity; no finite K/full verification/go.

- [x] Checked complete paired keccak256 body and real caller: actual zeroing,
  all full blocks, remainder declaration, final padding/absorption, both
  digest-output paths and all scopes. Equal selected buffer memory gives
  identical digest words and complete FFI event histories despite unrelated
  code/private memory differences. Allocated EntryData/code/domain/endian,
  input/output buffer agreement and clock premises remain explicit; they still
  need map-layout/decoded-input reachability and joint constructor transport.
  Source allowance202+20*floor(length/136),caller+1 is not target K. Successful
  keccak256-buffer-agreement-v2.log723targets, allowed axioms; index4579/7506,
  policy61444entries/2253269038bytes. Infinity; no finite K/full verification.

- [x] Checked public-memory/event agreement for actual Keccak permutation
  calls, all17 aligned/unaligned XOR lanes, complete block absorber/caller,
  and arbitrary full-block loops. Required helper code entries may agree
  while unrelated code/private table words differ. Exact array reads and
  tail-first byte-array writes, including failed stores, are related.
  Paired full-block loops preserve selected public words and identical FFI
  events with exactly20 source clocks/block in each run. Padding/output/full
  hash and whole original/radix map-context refinement remain open. Successful
  keccak256-paired-loop-v1.log699targets, permitted axioms; index4567/7468,
  policy61432entries/2253201027bytes. Infinity, no finite K/full verification.

- [x] Checked original full witness lookup directly from final Built/History/
  Records, deriving all mapped record-cell premises from actual record values.
  It returns exactly the last matching slice in the radix API's tuple format,
  for every query at every alignment. Dictionary value mapping/membership and
  record-address inversion check; no unique-hash assumption. Source body
  <=6*input.length+3 Pan clocks, preserving memory/control. Actual cross-program
  hash/digest/event/private-memory relation and whole-context refinement still
  open. `mutable-witness-dictionary-lookup-v2.log`1331targets, permitted axioms;
  index4558/7446, policy61423entries/2253142829bytes. Infinity; no finite K.

- [x] Checked entire actual original nodedb_build: retained power-of-two
  capacity selection, actual table allocation/clearing, every hash/set record
  iteration, table return and all scopes. Final Built/History/Records provides
  last-record-wins dictionary representation for exactly N observed digest/
  record pairs. Heap cursor/control result matches the real allocations.
  Conditional original source-clock allowance is quadratic in N and is not
  a target bound. Decoded records, arena/code/globals/heap premises still
  need whole-guest reachability, and original/radix actual digest/event/context
  refinement remains open. `mutable-witness-execution-v2.log`1360targets,
  permitted axioms; index4555/7440. Infinity; no finite K/full verification/go.

- [x] Checked complete actual original witness-record while loop, including
  hash-control/context transport, actual new/duplicate map updates and input
  ordinal advancement. Final Built/History covers exactly N observed digest/
  record pairs, with preserved slice records and all non-index locals. History
  values point to real input record addresses. Conditional loop allowance
  `(Keccak256.price(maximum)+7*N+9)*remaining` is only a source-clock bound.
  `mutable-witness-loop-v2.log`1325targets, permitted axioms; index4551/7434.
  Allocation/capacity/caller setup, actual final lookup API and original/radix
  digest/context relation remain open; infinity, no finite K/full verification.

- [x] Checked one complete original witness-builder record iteration:
  actual pointer/length loads, full real Keccak call, observed digest word/
  byte view, complete new/duplicate setter call and ordinal increment. Table
  invariant survives hash writes before its private allocation; record words
  survive hash and setter stores. Exact fixed original builder AST agrees
  with reused capacity/hash fragments. `mutable-witness-record-step-v1.log`
  1322targets, permitted axioms; index4548/7429. Ready, actual record words,
  buffer arenas/separation, code/domain/clock premises explicit. Whole record
  loop, constructor/caller connection and original/radix digest/context
  noninterference still open. Claim infinity; no finite K/full verification.

- [x] Checked complete original immutable-table raw insertion and setter,
  including actual header/hash/find/raw-call/copy/store/scoping and duplicate
  updates. Built invariant ties physical header/key/used/value/count to a
  logical insertion history. Actual constructor initializes it; raw insertion
  and both setter branches extend it with last-record-wins semantics. Real
  setter caller restores locals and pays<=7*processed+7 Pan clocks; no growth
  from Ready capacity/count bounds. All stores preserve earlier memory below
  the private table. Actual witness record loop/keccak/input-layout connection,
  whole original/radix caller refinement and target/global bounds remain open.
  Successful mutable-original-set-closure-v1.log1192targets, permitted axioms;
  index4543/7420; claim infinity, no finite K/full verification/global go.

- [x] Checked real32-byte insertion copy/post-copy tail, all seven header
  declarations and hash/index/scoping lift. Full insertion memory formula
  preserves header/other words and represents the updated keys, binary used
  bytes, values and incremented count. Concrete six-pool constructor layout
  discharges key/used/value copy/store/metadata separation and mapping/range
  premises, including cap4 padding. Source aligned hash bytes/words and
  Ready/domain/count/index bounds remain explicit. Whole body scan/tail
  composition, header preservation specialized to layout, no-growth setter
  and actual build trace remain open. Successful
  mutable-layout-representation-v1.log1171targets, permitted axioms;
  index4529/7397, claim infinity; no finite K/full verification/global go.

- [x] Checked original table initialization and real insertion components:
  both actual used-array clearing paths establish all-zero flags; final
  constructor header/count and empty KeyModel follow. Raw scan derives an
  empty slot and occupied insertion path from represented bytes/covering
  history, paying one Pan clock per occupied slot. Exact value/used/order/
  position/count suffix stores, existing-key setter return and false growth
  guard under count<=N,cap>=2*N+2 check. Value-cell writes preserve represented
  values/keys under explicit physical separation. Complete insert body/copy/
  header/hash composition and physical representation preservation remain
  open. Success mutable-empty-insert-closure-v1.log1162targets, permitted
  axioms; index4515/7365. Claim infinity; no finite K/full verification/go.

- [x] Checked complete original32-byte htab_find_slot/get and nodedb_lookup
  against a represented dictionary, at every query alignment. Actual hash,
  comparator, value-cell load, tuple ABI/return, record pointer/length loads
  and lexical frames compose. Find/get/lookup bodies cost at most
  6*order.length+1/+2/+3 Pan clocks. Physical headers, binary used/key/value
  representation, no-gap placement, dictionary relation, covering list/room,
  pointer ranges, record cells, code and clocks remain explicit premises.
  Actual construction/stores maintaining those premises, whole original/radix
  refinement and target pricing remain open. Successful logs
  mutable-get-call32-v1.log and mutable-nodedb-dictionary32-v1.log1132targets;
  permitted axioms, index4501/7337, incremental policy61366entries/
  2252890183bytes. Claim infinity; no finite K/full verification/global go.

- [x] Checked linear-table placement/dictionary model: cyclic distance, sound
  and complete lookup under occupied paths; safe updates/insertions preserve
  placement, uniqueness and dictionary overwrite. Fixed-capacity construction
  gives last-record-wins, an input-length covering list and abstract agreement
  with the radix model for every key. Actual byte-chain decisions now equal
  model search under physical key/used-byte representation; absence matches
  the dictionary under placement. Source mutating stores/count/ownership and
  whole map refinement are still open. Logs `mutable-placement-build-v1.log`
  and `mutable-find-model32-v1.log`; permitted axioms, index4490/7322,
  policy61355entries/2252845514bytes, infinity. No finite K/full verification.

- [x] Checked complete original htab_find_slot body/caller for32-byte keys at
  every alignment. Both real hash paths return the same byte-level keyHash;
  all32 unaligned loads and aligned-word reconstruction check. Real header
  declarations, hash ABI/call, masked index, memeq scan, returns and scoped
  caller compose. Body/caller <=6*order.length+1/+2 Pan clocks, preserving
  memory/control. Physical header/used/order/key views, room, power-of-two
  capacity, code/domain and clock premises remain explicit. Relating the
  covering order list to HT_COUNT, preserving it under mutations,20/52/60-byte
  keys, dictionary refinement, target pricing and global K remain open.
  `mutable-find-call32-v1.log`1119targets, permitted axioms; index4486/7304.
  Policy61351entries/2252820057bytes, infinity, no full verification.

- [x] Checked actual original32-byte table find scan and absent-cap return,
  including real memeq ABI/body/call at all key alignments, early equality,
  masked increment and lexical restoration. From explicit physical table
  premises (binary used bytes, occupied-order coverage, room, power-of-two
  capacity, key/query views, code and clocks), scan costs<=6*occupiedCount
  Pan clocks and preserves memory/control outside locals/clock. Probe slots
  are distinct before wrap and the first empty lies within occupiedCount.
  `mutable-masked-path-v2.log`1107targets, permitted axioms; index4476/7284.
  Header/hash/caller setup, mutations maintaining the representation, other
  key lengths, last-wins map refinement and target pricing remain open.
  Policy61341entries/2252767802bytes, infinity; no full verification.

- [x] Checked actual U256 equality body/caller and both literal SSTORE state-fee
  guards. Given honest original/current/next values, actual0/1 predicates
  satisfy charge+old per-slot debt=refund+new debt. A conditional zero-start
  ledger never refunds more than charged. `gas-storage-classify-v3.log`
  1164targets, permitted axioms. Backend/journal/created-account invariants,
  actual fee/rollback projection and global signed state use remain open.
- [x] Checked conditional block-gas accounting before ordinary refund,
  reservation/completed-counter bounds and a final uncommitted transaction.
  Actual BO_GAS_USED store is identified in the fixed AST and executes with
  natural no-wrap addition under the200M bound. Source TX_BASE is12000, not
  21000; conditional completed-count ceiling16666. Fee/pool/state premises are
  still open. `gas-block-accounting-v1.log`1165targets, permitted axioms;
  index4469/7263, incremental policy61333entries/2252730199bytes, infinity.

- [x] Checked actual successful-child counter/spill repayment prefix. The
  literal child-error caller, spill addition, mutable minimum and three real
  repayment stores produce parent regularBudget=old parent+old child, under
  actual frame separation/code/clock and combined budget<2^64. The arbitrary
  continuation retains rep's lexical scope. The real log/table suffix's memory
  frame is still open. `gas-child-success-v4.log`1116targets, permitted axioms.
- [x] Checked conditional arbitrary-forest counting: each production contributes
  once per enclosing edge, so propagation<=depth*productions; uniform occupancy
  then bounds weighted propagation using aggregate paid production, without
  summing declared root gas. Scenario30M/5000 keys, depth538, aggregate380M gives
  245368888000 units. `gas-merge-budget-v1.log`1173targets; index4464/7236.
  Runtime event/merge/occupancy/depth/gas coupling and actual prices remain
  open. Incremental policy61328entries/2252704190bytes; claim infinity.

- [x] Checked conditional actual-calculator decay algebra: the access/value
  fee premises imply child<=capNat(parent-100); shifted contraction is
  64*(child+6237)<=63*(parent+6237). A chain with root<=30M and those premises
  at every edge has depth<=538. Success `gas-nested-decay-v1.log`1172targets,
  permitted axioms; index4460/7228. Actual trace/root premises remain open.
  `nested-resource-pilot.json` compares exact single-wave and greedy repeated
  waves. Repeated waves can exceed the single-wave maximum by about8x in the
  relaxed model; neither is an arbitrary-forest or runtime upper bound.
  No global go, target pricing, finite K or full verification follows.

- [x] Checked both actual saturating-add branches and its unconditional lower
  bound on the first argument. Actual up-front value-fee computation/charge
  establishes used-counter credit>=11300 even for saturated memory costs;
  unaffordable fees raise before continuation. Prefixes are literal subtrees
  of CALL/CALLCODE; DELEGATECALL/STATICCALL literally supply a zero value and
  have zero stipend. Success `gas-value-fee-sites-v1.log`1171targets, permitted
  axioms; index4459/7220. Access<=3000, actual input/cell/code/clock and natural
  counter no-wrap premises remain explicit. Still connect every intervening
  helper and successful child return to the full frame/block invariant.

- [x] Checked complete actual call-gas calculator in the zero memory/extra-cost
  mode and its real five-argument/two-word caller. The requested gas is any
  64-bit word; actual 63/64 cap/clamp bounds the debit, stipend is0or2300.
  Body/caller cost2/3Pan clocks. All four fixed call opcodes pass the proved
  zero-cost arguments and contain the actual charge/counter-debit prefix.
  That prefix checks with its real charge_gas call and subtraction: under
  actual cell/code/clock, funded stipend and no-wrap premises, resulting parent
  regular budget + forwarded child seed = previous parent budget. Success
  `gas-forward-sites-v6.log`1168targets, permitted axioms; index4456/7210.
  Still need fee-to-prefix entry, child initialization/successful return,
  signed state/block conservation and global positive-charge/table coverage.

- [x] Checked source-level charge_gas bodies/callers on affordable and actual
  out-of-gas paths. Successful callers debit liquid and credit the used counter
  by the exact natural amount and preserve regular budget; failures raise
  EvmErr4 before stores. Each caller costs1Pan source clock (the existing
  compiled Stack summary has its separate clocks/Work). Actual cells/code,
  affordable and liquid+used<2^64 remain explicit. Successful
  `gas-regular-charge-call-v1.log`1115targets, permitted axioms; index4447/7185.
  Whole-run source/compiled alignment and aggregate gas remain open.

- [x] Checked actual frame_halt and child-error incorporation bodies/callers.
  Halt moves liquid gas into used and zeros liquid, preserving regular budget.
  Child-error return executes all three parent additions and preserves unread
  child counters from parent writes under explicit frame separation. Its exact
  budget equation accounts for the omitted child spill; parent resulting
  budget<=the two previous budgets combined. Actual callers cost1source clock.
  No-wrap sums/readable cells and frame separation remain entry premises;
  successful-child continuation and forward/stipend debits remain open.
  `gas-child-error-call-v1.log`1113targets, permitted axioms; index4445/7179.

- [x] Checked both affordable paths and the actual out-of-gas path of
  charge_state_gas, plus real ignored callers. The reservoir branch returns
  directly; spill branch executes add_sat, actual debits/spill stores and
  scopes; unaffordable branch raises EvmErr4 before any pool store. Successful
  calls preserve the natural regular budget and cost<=2 source clocks; failed
  calls cost2 and preserve memory/control. Explicit premises include
  state_left+gas_left<2^64, gas_left+spill<2^64, actual frame cells/code and
  clocks. Successful `gas-state-charge-call-v1.log`1109targets, permitted axioms;
  index4441modules/7167facts. Global initialization/call-tree conservation open.

- [x] Checked actual state-gas refund and rollback-refill bodies/callers.
  Their real stores preserve gas_left+regular_gas_used+outstanding_spill when
  gas_left+spill<2^64; mapped/stored frame cells, runtime code and refill
  reservoir-cell separation remain explicit. min returns the actual unsigned
  minimum; ignored refund/refill callers cost2/1 source clocks. Successful
  `gas-refund-calls-v1.log`1102targets, permitted axioms; index4434/7155.
  This is local conservation, not global gas coverage or target pricing.

- [x] Checked the complete actual encode_header body/caller and the complete
  block_rlp_length body/caller, followed by the exact payload_header 8MiB guard.
  Header size<=916, body/caller clocks<=1345/1346; block body/caller clocks
  <=12*Ntx+43*Nwd+1381/1382. The real block result is >=25*Nwd without wrap;
  successful continuation past the actual guard therefore gives Nwd<=335544.
  Actual heap release restores globals; writes preserve old header/input/record
  cells. Decoded data, field-byte Arenas, extra<=32, fresh-buffer geometry,
  code/domain and clock affordability remain explicit entry premises. This
  discharges the former assumed preceding-header-size bound, not global entry
  reachability or target steps. Successful `input-block-guard-v3.log`1393targets,
  only permitted axioms; index4429modules/7139facts. Claim remains infinity.

- [x] Checked the actual header field sequence and all four field kinds:
  pointer/scalar/quad reads from preserved old header memory; writer calls,
  real p/w updates and right-nested continuation; natural aggregate pointer/
  clock bounds and re-established memory/domain/heap context. Literal AST
  decomposition proves21 base+2 optional descriptors. The actual list-header
  writer/caller also checks. Whole header composition is now checked above;
  builder entry premises remain open. Earlier closure `input-rlp-list-write-v1.log`1167targets, permitted
  axioms; index4416modules/7111facts at that earlier checkpoint. No finite certificate.

- [x] Checked complete actual rlp_put_u256 and its real declaration/assignment
  callers: heap mark, alloc32, minimal writer, byte encoder, heap release,
  return and all scopes. The heap global is restored exactly; encoded size is
 1..41, body/caller costs<=124/125 source clocks, and memory outside output/
  temporary ranges is preserved. Domain, heap-room and buffer extents remain
  explicit. Closure `input-u256-put-call-v1.log`1159targets, permitted axioms.

- [x] Checked complete actual u256_to_be_min: <=32 bytes, <=67 body/68 caller
  source clocks, real limb calls/masked shifts/stores, temporary scope cleanup,
  and outside-buffer memory frame. Actual heap_mark/heap_release callers also
  check. Byte-encoder access premises now follow from natural ordinary-memory
  source/destination extents. Successful closure:
  `input-rlp-write-access-v2.log`1154targets, permitted axioms only. Next is the
  temporary allocation/release in rlp_put_u256, then whole header/block prefix.

- [x] Checked real byte-encoder declaration/assignment callers retaining written
  memory; actual six-stage bit_length64 returns<=64; actual u256_bit_length
  chooses a limb and returns<=256; actual u256_byte_length returns<=32 with
  no-wrap rounding arithmetic. Body/call costs are0/1,1/2,2/3 source clocks
  respectively. These prepare the U256 header writers; whole header/block
  prefix and global certificate remain open. Successful closure:
  `input-u256-byte-length-v2.log`1146targets, permitted axioms only.

- [x] Checked actual RLP encoding writers: put_be loop/body/caller with one
  source clock per byte and real store frames; whole scalar and header writers
  return1..9 bytes in<=18 body clocks. Their real callers retain written memory.
  Whole byte-string encoder includes both special-case reads/stores and actual
  arbitrary-alignment/overlap memcpy, returns<=n+9, and costs<=n+20 body clocks.
  Concrete mapped-access/code premises remain; whole encode_header and block
  prefix/guard are still open. Successful joint closure:
  `input-rlp-byte-write-built-v1.log`1139targets, permitted axioms only;
  index4388modules/7038facts. This is source execution evidence, not finite K.

- [x] Checked the full actual block tail from the transaction-loop test through
  its return. Actual decoded records supply every pointer/length/conditional
  byte read, and their raw lengths telescope to the slice length. The real
  transaction sum is <=436207564; the composed tail costs at most12*Ntx+43*Nwd+33
  source clocks and its result is >=25*Nwd without wrap. The preceding encoded
  header total<=2^31, phase entry and outer size guard remain explicit/open.
  Evidence: `input-rlp-transaction-phase-v2.log`1337targets, permitted axioms;
  index4374modules/7012facts. Whole certificate still infinity.

- [x] Checked actual RLP scalar/header helpers, whole withdrawal size function,
  withdrawal accumulation loop and final block-length suffix. From explicit
  copied-record/code/phase-entry premises, including preceding total<=2^32,
  the actual result is at least25*N without64-bit wrap, with at most43*N+22
  source clocks. Thus passing8MiB implies N<=335544 **at that phase**. Deriving
  its entry and preceding-total premises from the whole block function remains
  open. Evidence: `input-rlp-withdrawal-phase-v2.log`1127targets, only permitted
  axioms; index4360modules/6988facts. No finite certificate or target-step bound.

- [x] Measured all 33,614 EEST records: 33,605 normal passes, 9 expected malformed passes, no failures. These are **Spike instruction counts**, not formal evaluator steps. Evidence: [Phase 1 report](work/agent-notes/PHASE1-REPORT.md).
- [x] Documented artifact hashes, Spike/formal-clock differences, synthetic inputs, zero-user-gas witness work, and a quadratic hash-table collision example. The numerical envelope remains **unproved**.
- [x] Checked an exact 23,132-step bootstrap theorem, subject to explicit baseline ROM/configuration premises.
- [x] Checked substantial quantitative compiler lemmas and complete fixed Crep/Word/Stack table checks. **The end-to-end compiler/state/oracle connection is not complete.**
- [x] Checked weighted Stack work accounting and local bounds for memzero, guarded allocation, affordable gas charging, and parts of memory expansion.
- [x] Checked the **complete** zero-expansion and nonzero/no-capacity-growth executions of `extend_memory`, under their stated entry premises. The capacity-growth case is unfinished.
- [x] Checked allocation at every initial clock, the real allocator call, its return continuation, and saved-state transfer. **Caller setup and the global invariants establishing their premises remain open.**
- [x] Committed all proof work through `04603be4d`. The evidence index contains 3,834 module hashes and 5,898 printed theorem facts; these counts are not percentages. No proof build was left running at that checkpoint.

## Historical feasibility review — numerical gate retired

- [x] Rechecked all 3,834 indexed proof-source hashes: no mismatches. Claim remains infinity, worktree was clean at review start, and no proof build was running. This checks checkpoint integrity, not verification.
- [x] Identified the exact Named Stack initial state and a route through existing compiler proof components. The interfaces in Section 3.R2 are **designs, not newly checked theorems**. Avoid redoing quantitative proofs of the earlier compiler passes.
- [x] Audited the major work categories and found six independent system calls, two user gas counters, and unmetered witness-table construction before transaction/header validation. Several global bounds remain unknown; see Section 3.R3.
- [x] Ran a cheap numerical pilot: the current basic-block accounting assigns 37 Work credits to one raw insertion probe body. At the existing conversion rates, a triangular probe allowance for 3,728,269 records costs **24,686,375,150,371,392**, already about **2.74 times the entire score cap**, before other work. Collision reachability is unproved; this diagnoses an overly loose upper bound. Evidence: [budget script](work/agent-notes/feasibility-budget.py), [results](work/agent-notes/feasibility-budget.json), Section 3.R1.
- [x] Completed Section 3.R4's first witness-table investigation. Derived `F ≤ D(D−1)/2 + Σ(m_r−1)r`, `R ≤ D(D−1)/2`, hence `F+R ≤ D(N−1)`, and the distinct-preimage length constraint. These are paper arguments under explicit table invariants, **not Lean theorems**. Inspected the fixed Padded79/185/188 paths and checked the relaxation against 186,368 small table executions, 2,050,048 later queries and 1,616 independent optimizer comparisons. Evidence: [script](work/agent-notes/witness-table-budget.py), [results](work/agent-notes/witness-table-budget.json), Section 3.R5.
- [x] Checked `WitnessRadix/Model.lean`, `Compact.lean` and `Space.lean`: arbitrary-key last-wins construction; actual BitVec256 instantiation with at most 257 query-node inspections, including absent keys; at most N branches; and 32N hash bytes plus 24 bytes per branch fitting in the original `32*cap` allocation when `cap ≥ 2N+2`. Main theorem prints use only permitted axioms. Evidence: successful `logs/witness-radix-space-v1.log`, indexed in `proof-checks.json`. No machine/refinement claim is made.
- [ ] Current-program accounting still needs a justified later-query count Q and useful probe allowances. There is no requirement to fit a numerical cap and no replacement route.
- [ ] Connect the existing baseline compiler/entry interfaces after deriving the original program's global bounds. No numerical feasibility gate applies.
- [ ] Close the remaining coverage/budget unknowns and establish a justified finite K for the unchanged implementation, with no numerical ceiling.

## Original implementation proof obligations (read with current scope above)

- [ ] Prove input/gas-reader correspondence and initialization of the global guest invariant.
- [ ] Prove a global work/clock potential covering calls, refunds, frame reuse, parsing, witnesses/state, table collisions, output, and covered failure/unwind paths.
- [ ] Complete the capacity-growth path and any other local summaries **actually required by the chosen global proof**; prove their entry premises at every use.
- [ ] Connect bounded execution through the actual compiler artifacts, bootstrap, oracle/FFI, and matching-result relation.
- [ ] Prove and report a literal finite K for the current implementation, with explicit units, assumptions and only permitted axioms. No score cap or Yukon promotion is required.
- [ ] Refresh policy/transport checks for the final package. The 2026-10-17 incremental policy check passes and includes all current Solver modules (61,323 full-package entries; 2,252,675,043 bytes); this is not isolated verification or a final overlay check.
- [ ] Obtain final verification on a suitable, authorized host. **The user prohibited the full audit/full verifier on this machine.** No isolated finite-certificate verification has occurred.

**Latest checked connection:** `QueryExecution.lookup_built` proves the complete actual candidate lookup from concrete HOL memory/header/ABI/code premises: exact last-record-wins result, at most **262 source clocks**, and preserved nonlocal state. Successful closure: `witness-radix-query-function-v3.log`; only permitted axioms. Construction must still establish the represented-memory premise, and source clocks are not target transitions. The actual fixed `memeq` 32-byte aligned and unaligned paths, actual caller restoration, and real code-entry argument environment now check with only permitted axioms (`witness-radix-memeq-environment-v4.log`). The comparison consumes at most four source clocks plus one call clock. The candidate compiler reports 905,572 code bytes, 4,615 bitmap words and a static stack bound of 538 words (`witness-radix-static-depth-v1.log`); these are development compiler results, not a target certificate.

**Construction connection:** actual copy and zero-count loops now check from concrete array/key-byte premises, each consuming one source clock per ordinal. Copy has exact memory/row/frame facts; count preserves all other locals and nonlocal fields. `ScatterProgram.loop_partition` now proves the complete actual stable-scatter loop equals two ordered filtered block writes, with final cursor/index values, one source clock per ordinal and preservation of other locals/nonlocal fields. The outer agenda and completed-graph relation remain open. Successful closures: `witness-radix-count-copy-v1.log`, `witness-radix-scatter-partition-v1.log`.

**Outer construction connections:** the literal thirteen-declaration entry prefix now follows from actual ABI/header cells, with checked entered bindings and local-only restoration. The complete empty helper writes only root zero at no source-clock cost. The final terminal leaf-store/outer-loop iteration pays exactly one source clock. The complete pending-task pop loads actual suffix cells, changes only five task locals and returns continue with no further memory/clock change. Existing-model terminal/unary/split equations are checked. Successful closures: `witness-radix-build-cases-v2.log`, `witness-radix-terminal-loop-finish-v2.log`, `witness-radix-pop-body-v1.log`. Leaf-store/pop composition and the actual terminal outer-loop resumption now check with explicit store separation. The complete unary outer iteration also checks, including counting and restored temporary counters: only bit and clock change, with exact input.length + 1 source-clock payment (`witness-radix-outer-transitions-v1.log`). The literal branch-allocation/pending-right push now checks with exact seven mapped stores and five persistent local updates, including scoped node restoration. The combined scatter/copy prefix, both resets and arbitrary continuation also check, with exact primary/backup sorted memory and 2*input.length source clocks (`witness-radix-sort-allocation-checkpoint-v1.log`). The complete split/count scopes and outer-loop resumption now check, with exact 3*input.length + 1 source clocks and restored temporaries (`witness-radix-split-loop-memory-v1.log`). QueryFootprint proves that agreement on concrete subtree read words preserves the actual lookup representation (`witness-radix-query-footprint-v1.log`). OpenGraph now proves hole replacement, preservation of expected trees/pending order, and completion into the actual lookup representation. Actual split stores install that branch, select left locals, preserve child rows and push physical right-task cells under explicit parent separation/no-wrap premises; terminal loads follow from interval/getLast. Checked closure: `witness-radix-construction-graph-checkpoint-v1.log`. Logical agenda cost is at most 1028*N source clocks; cumulative frontier/leaf accounting keeps branches < N and concrete branch addresses are nonzero/even/fresh (`witness-radix-address-read-stable-v1.log`). BackingLayout/ImmutableRecords/LayoutContext now derive sorting read ownership and all seven mapped/distinct store cells from one allocation layout, valid ordinals and readable task rows. Full splits preserve immutable records/keys and next-left ownership, and update the concrete context (`witness-radix-layout-child-v1.log`). Located partial graphs have every actual read classified into immutable data or the installed branch arena (`witness-radix-layout-located-v1.log`). The actual split body now installs its branch from the shared layout/located/safe-frontier invariant; no separate per-read/per-store premises are assumed. Checked postconditions retain expected-tree representation, graph location, safe remaining frontier stores and distinct slots (`witness-radix-layout-checkpoint-v1.log`, 690 targets). The complete actual split body now re-establishes the full assembled construction invariant, including physical pending stack, exact readable current/pending intervals, valid task metadata, graph representation/location/safe/distinct/aligned frontier and allocation budget (`witness-radix-invariant-split-checkpoint-v1.log`, 734 targets). Terminal bodies for both continuation and final return are derived from shared invariant components; leaf graph/frontier/data/row preservation also checks. Unary and terminal continuation now also execute the actual body and re-establish the complete invariant. The final terminal case returns and supplies the complete actual lookup representation at the original table root slot. Successful closures: `witness-radix-invariant-root-checkpoint-v1.log` (735 targets) and `witness-radix-invariant-finish-v1.log` (727), only permitted axioms. The whole actual while loop now terminates from the complete invariant and 4*agendaWeight clock affordability, returns the expected represented tree at the original root, preserves other control fields, and consumes at most 4*agendaWeight source clocks (`witness-radix-loop-termination-v2.log`, 741 targets, only permitted axioms). The initial 256-bit agenda gives 1028*N once initialized. InitialContext/InvariantInitial establish that invariant from the real entered bindings and initialized mapped/readable arrays. HelperBuilt proves the complete literal helper, including prefix loads/tests/lexical scopes and empty case, with expected represented tree, preserved control fields and at most 1028*N source clocks (`witness-radix-ordinal-array-v1.log`, 748 targets). OrdinalArray checks the actual 0..N-1 initialization and entry ordering. Establishing the hashed arrays/layout from nodedb_build/htab_new and relating the original maps remain open; source clocks are not target transitions.

**Constructor suffix:** the entire fixed aligned/separated 32-byte memcpy, real ABI/code lookup and ignored-result call now check: exact four-word copying, preserved caller locals/nonlocal fields and two source clocks. The literal nodedb_build after-hash suffix composes that call, record-pointer/ordinal stores and increment (`witness-radix-constructor-copy-v2.log`, 615 targets, permitted axioms only). Actual hashing, allocation, prefix preservation and whole constructor initialization remain open.

**Constructor invariant connection:** the actual after-hash iteration now derives all six mapped/distinct store cells and scratch/key separation from shared layout geometry, preserves earlier hash bytes and fixed header/records, and establishes the next initialized prefix with exact locals/clock. On completion that prefix supplies all immutable/ordinal-row helper premises. The real helper call and constructor table-return tail now check within 1028*N+1 source clocks (`witness-radix-constructor-step-v3.log`, 774 targets, permitted axioms only). Hash calls and htab_new/allocation initialization remain open.

**Allocation connection:** the complete successful fixed persistent allocator and actual lexical call now check, including heap global update, returned pointer, natural guard/alignment/monotonicity and exact one call-clock cost. Concrete aligned arena addresses imply mapping in the challenge ordinary domain. Exact htab_new allocation offsets, including padding after the used-byte array, imply the full layout Valid/Mapped properties (`witness-radix-allocated-layout-v1.log`, 669 targets, permitted axioms only). Actual htab_new allocation/memzero/store composition and reachable heap-room facts remain open.

**Aligned clearing connection:** the complete fixed memzero on aligned word-multiple ranges now checks, with both real word loops, skipped byte loops, lexical restoration/return and actual ABI/code call. Exact call cost is floor(n/32)+floor((n%32)/8)+1 source clocks; exact final memory and a complete frame outside the range also check (`witness-radix-zero-call-v1.log`, 624 targets, permitted axioms only). The initial four-byte table case and actual htab_new composition remain open.

**Short clearing / table composition:** the actual byte store, tail loop, complete short aligned memzero and real call now check, including the cap=4 case at five source clocks and an exact frame outside its one word. ProgramPrefix checks composition of actual declarations/allocator calls/commands and lexical restoration. TableNewProgram extracts the entire literal htab_new action sequence; AllocationExpected supplies natural expected-cursor allocation steps. Concrete execution evidence for that whole sequence remains open (`witness-radix-allocation-expected-v1.log`, 636 targets, permitted axioms only).

**Complete table creation:** the whole literal fixed htab_new for 32-byte keys now checks from actual ABI/domain/code/heap-cursor and natural allocated-layout room/cap-shape facts. All six allocator calls, nine header stores, both clearing cases, scopes and table return are included. Exact nonlocal state/heap/memory/source-clock facts check: clearCost(cap)+6 clocks, hence 11 for cap=4 or floor(cap/32)+floor((cap%32)/8)+7 for word-multiple capacity (`witness-radix-table-state-v2.log`, 699 targets, permitted axioms only). Header contents/record frames, actual caller setup and reachable heap-room facts remain to connect.

**Actual constructor preparation:** TableMemory/Records derive the four real helper pointer fields and complete frame for earlier decoded records. TableEnvironment/Call include actual htab_new arguments/code/callee, memory/heap result, lexical return binding and caller restoration. ConstructorPrepare connects that real call and the literal three array loads/zero ordinal declaration to the remaining actual record loop, with mapped arrays, fixed header/records, empty initialized prefix, exact live locals and source-clock payment (`witness-radix-constructor-prepare-v2.log`, 718 targets, permitted axioms only). Natural layout/cap/heap room and decoded-record premises still need global derivation; capacity loop and hash calls remain open.

**Capacity connection:** the literal initial cap=4 declaration and complete real doubling loop now check in at most 30 source clocks for N<2^31. The chosen power-of-two cap satisfies 2N+2 ≤ cap ≤ 4N+4 and cap ≤ 2^32, is 4 or divisible by eight, and all other locals/nonlocal fields are preserved. CapacityEntry exposes the actual htab_new continuation. The N<2^31 fact follows from natural allocated record-array/heap-room bounds; their global reachability remains open (`witness-radix-capacity-entry-v1.log`, 586 targets, permitted axioms only). Hash calls remain the next constructor execution gap.

**Keccak permutation connection:** the fixed source oracle returns exactly 200 bytes; the actual external call, permutation function and real caller now check with exact memory/event update and one call clock. Successful reads follow from 25 aligned mapped state words, and the byte writer preserves cells outside the state region. Generic actual byte-copy stores and the fixed eight-byte/tail block shapes also check (`witness-radix-copy-byte-v3.log`, 652 targets, permitted axioms only). This does not yet cover full keccak256 absorption/padding or its constructor call.

**Complete generic copy:** the entire actual fixed memcpy now checks for arbitrary alignment, overlap and mapped ranges: all four loops, branch selection, scopes/return, real code/argument/callee environment and caller restoration. Exact memory and source-clock cost are exposed; body cost ≤ length and call cost ≤ length+1. Cells outside the destination byte/word footprint are preserved (`witness-radix-copy-general-call-v1.log`, 640 targets, permitted axioms only). This closes the final-block copy execution gap, but full Keccak absorption/padding and constructor composition remain open.

**Complete block absorption:** the whole fixed keccak_absorb_block now checks for aligned and expanded unaligned loads, all 17 actual XOR/store iterations, real permutation call, scopes/return and real caller/callee/code environment. Exact cost is 18 body / 19 call source clocks; caller locals restore, globals/code/oracle/host preserve, and memory outside the state footprint preserves (`witness-radix-keccak-absorb-call-v1.log`, 678 targets, permitted axioms only). Full keccak256 block iteration, padding and output remain to compose.

**Complete hash execution:** the entire fixed keccak256 and real caller/callee/code/arguments now check: initial clear, arbitrary full-block loop, remainder scope, padding clear/copy/stores (including rem=135), final absorption, both digest-output paths, scopes/return and caller restoration. Body cost ≤ 202+20*floor(length/136), call cost ≤ 203+20*floor(length/136) source clocks. Globals/code/oracle/host and cells outside the three buffers preserve (`witness-radix-keccak256-call-v1.log`, 702 targets, permitted axioms only). Actual global pointers and mapped-buffer premises remain explicit; their allocation/input derivation and constructor hash-loop composition are next.

**Complete constructor population:** natural arena/alignment bounds now derive all hash mapping and outside-buffer frames. Real constructor record loads feed the complete actual hash/copy/store/increment iteration; the entire record loop initializes hashes, record pointers and ordinals while preserving earlier rows and fixed records. Its composition with the radix helper and table return establishes the actual expected lookup representation at the stored root. Bounds are ≤1374*N+1 source clocks for maximum node length 1024 and ≤10854*N+1 for maximum code length 65536 (`witness-radix-constructor-populate-v3.log`, 874 targets, permitted axioms only). These remain conditional on allocated buffers, decoded records and code/global facts; table/capacity entry, their global reachability, original-map refinement and target certificate remain open.

**Complete constructor execution:** the full literal candidate nodedb_build and real caller/callee now check, including initial capacity selection, every table allocation/clear/header write, array setup, all actual hash/copy/store iterations, whole radix helper, all scopes and table return. Final memory represents the expected tree at the stored root and advances heap_ptr exactly. Body bounds are ≤1378*N+47 source clocks for maximum length 1024 and ≤10858*N+47 for maximum 65536; the real call adds one (`witness-radix-constructor-call-v1.log`, 915 targets, permitted axioms only). The entry premises explicitly include decoded records, actual globals/code, allocated buffers before the records and conservative natural heap room. Their reachability, relation to the original fixed source maps and target/global certificate remain unproved.

**Actual input-copy connection:** the full literal input_blob passing-size/allocation path now checks from actual oracle/host/domain/code/heap facts. It reads the encoded mathematical input length modulo 2^64, executes the real guard and allocator, derives every host/ordinary mapping, copies all words, restores scopes and returns the actual pointer/length pair. Exact cost is ceil(encoded_length/8)+1 source clocks, at most 16,777,215. No mathematical input-list size assumption is introduced. Successful closure: input-blob-execute-v3.log, 695 targets, permitted axioms only. Copied heap-byte correspondence, oversized/allocation-failure paths, actual SSZ/gas guards and global certificate remain open.

**Copied heap-byte connection:** BlobBytes.execute_bytes now combines whole actual input_blob execution with exact little-endian heap-byte equality over the encoded input extent and the 16,777,215 source-clock ceiling. CopyMemory supplies exact copied words and untouched cells; ByteDecode/CopyBytes prove actual subsequent byte loads (input-blob-bytes-v1.log,1024 targets, permitted axioms only). Oversized mathematical lists may have nonzero bytes after the encoded extent; no zero-tail/mirror shortcut is used. WordAssemble separately checks 4/8-byte bitwise-to-natural LE assembly (input-word-assemble-v4.log). Actual SSZ guards/gas reads and fresh-heap invariants remain open.

**Actual payload gas read / offset validation:** ScalarProgram/Scalar64 prove real expanded byte-load/shift/OR semantics; FlatAddress/FlatScalar connect flattened generated additions. PayloadGas extracts the fixed guest's exact gas-field store and bounds its actual expression by 200M under copied input, extent, payload-position and both container-offset premises (input-payload-gas-v3.log). SszFail checks the real exception call. OffsetsValidExecute checks the entire actual nonempty offset validator on ordered/in-range arrays with first=fixed, preserving all nonlocal fields except exactly count source clocks. OffsetsFaultStep checks both failing per-offset guards, exact exception propagation and one call-clock payment. Successful joint closure: input-offsets-fault-step-v2.log,1042 targets, permitted axioms only. The unrestricted array loop, normal-return inversion, actual decoder guards/positions and global reachability remain open.

**Unrestricted validator/caller connection:** OffsetsAnyLoop/AnyExecute cover arbitrary mapped offset words, including real range/order/final-equality rejection paths, at most count+1 body source clocks. OffsetsNormal derives first=fixed from a genuine normal return without assuming valid offsets. OffsetsEnvironment/Call/CallNormal include the actual four-argument ABI/code/callee and ignored-result call: at most count+2 clocks, normal resumption proves first=fixed and changes exactly the caller clock. HeapFrame proves copied-input bytes survive stores before/after their natural extent. Successful joint closure: input-heap-frame-v1.log,1116 targets, permitted axioms only. Actual decoder offset stores/positions, fresh-heap and global reachability remain open.

**First actual container-store/guard connection:** StoreScalar/HeaderProgram/HeaderPair/HeaderGuard now check the fixed decoder's first two real LD_LE32 stores and normal validator call. They derive le32(input,2)=16, 16<=le32(input,6)<=the passed container length, preserve the copied HeapInput bytes, and change exactly the caller clock after the two stores (<=4 clocks). Mapping/read/write separation follows from actual natural arena geometry. All unrestricted validator summaries now retain every checked range/order fact on normal resumption. Successful closure: input-header-ranges-v2.log,1120 targets, permitted axioms only. Entry still explicitly assumes shifted p=blob+2, at least10 encoded bytes, real globals/code/exception shape, mapped natural allocation geometry and an actual normal prefix execution. Schema/length entry, second request guard and reachable initialization remain open.

**Complete actual entry / first-container normal-return connection:** HeaderEntryProgram/Schema/Guards/Entry prove the fixed decoder entry on arbitrary copied input, with all three real SszErr1/2/80 rejection paths at one call clock and exact shifted continuation on passing checks. EntryNormal derives schema bytes and encoded length>=18 from an actual normal function return. HeaderReady/AfterNormal rule out every first-validator exception before continuation. HeaderFirstContainer composes them: a genuine normal decode_stateless_input return proves schema, le32(input,2)=16 and16<=le32(input,6)<=encoded_length-2, and exposes the actual next continuation with HeapInput preserved and <=4 source clocks so far. No valid-schema/first-offset premise is assumed. Successful closure: input-first-container-v1.log,1128 targets, permitted axioms only. Initial copied-memory/code/shape/natural allocation premises remain explicit; request/payload/witness remainder and global certificate remain open.

**Complete actual request-prefix connection:** RequestProgram/PrefixProgram/Load/Chain/Positions/Setup/PrefixEntry/PrefixNormal/FromHeader compose the fixed decoder's actual offset loads, real SI=alloc96 call, actual flattened chain-id LD_LE64/store, np/nlen declarations, all scopes and SszErr81 length rejection. From a genuine normal decode return, Request.from_header derives encoded length>=62, request pointer=blob+18, 44<=request length=witness_offset-16<=encoded_length-18, and exposes actual requestBody execution with HeapInput plus code/shape/domain/FFI/global-heap metadata. Prefix costs one allocation clock, or two through length rejection, and the complete prefix through first-container processing costs at most five clocks. Successful closure: input-request-from-header-v2.log,1140 targets, permitted axioms only. Entry still assumes natural 64-byte ssz_offs separation, a heap cursor after the copied input, 96 bytes of SI allocation room, runtime code/shape/domain facts and initial HeapInput; their reachability and second-container/payload/witness/global proof remain open.

**Next action:** execute the three actual request offset declarations, three ssz_offs stores and count3/fixed44 validator, deriving le32(input,18)=44 and bounded/ordered request slices. Connect payload position/extent, actual gas/record premises, reachable initialization/allocation, map/source refinement and whole-guest compiler/target bounds. **Current principal risk:** the original-map relation and whole-guest input/gas/query/composition proofs remain open; source clocks are not target transitions. No finite K or final verification exists. Historical stop instructions below are superseded by the current authorization above.

---

**Actual request/payload/gas entry connection:** RequestOffsetsProgram/Stores/Setup execute all three real declarations and word stores, preserving copied bytes and lexical scopes. OffsetsNormal covers all count-three validator outcomes and rules out rejected arrays before continuation, at most five source clocks. OffsetValues derives raw le32(input,18)=44, ordering/ranges, and the actual decode_payload call at blob+62 with contained slice le32(input,22)-44. PayloadProgram/Call/CalleeNormal check the real >=540 guard, SszErr50 propagation, two-argument ABI and normal-callee-return inversion. RequestPayloadFromHeader composes from genuine normal full decode_stateless_input execution: encoded extent>=602, both raw fixed offsets16/44, actual payload entry/copied bytes/code/domain/globals and a source-clock lower frame. RequestGasFromHeader proves the actual fixed gas expression at that entry is <=200M from the declared-gas premise. Initial runtime/code/copied input/natural ssZoffs/cursor allocation96 room remain explicit. The gas store after alloc136 and nested list decoding, global reachability, witness records, map/compiler/target/global finite certificate remain open. Successful joint closure input-payload-flat-prefix-v1.log,1153 targets, permitted axioms only. PayloadPrefixProgram extracts the literal alloc136/two stores/four offset declarations for the next connection. Claim is still infinity.

**Actual payload allocated prefix connection:** PayloadHeaderStores/OffsetDeclarations/PrefixSetup check the real alloc136 call, header pointer/length stores, all four copied scalar reads (raw input498/566/570/590), every scope and copied-input frame. PayloadOffsetsProgram/Stores/Normal check four actual ssz_offs stores and the unrestricted count4/fixed540 call, including all rejected arrays, <=6 source clocks. PrefixGuard composes from a genuine normal after-length-guard payload return, derives raw le32(input,498)=540 and all range/order facts, preserves HeapInput and pays <=7 source clocks including allocation. ExtraGuard/PrefixExtra cover real SszErr51 rejection and derive le32(input,566)-540<=32 before the actual transaction-list decode. Joint success input-payload-prefix-extra-v3.log,1163 targets, permitted axioms only. Entry still explicitly requires runtime/copied memory/aligned before-input ssz_offs64, heap cursor after input and alloc136 room; no global startup proof or final gas-store invariant is claimed. Next: the two extra-data stores, whole actual ssz_split_var_list and ssz_fixed_list_count calls/frames before the gas store; then record/witness/global/target connections. Claim remains infinity.

**Actual variable-list entry and header guards:** VarList.Program extracts the fixed ssz_split_var_list AST, including the real loop and final record-length store/return. Entry checks empty return, short SszErr20 rejection and actual copied first-offset declaration, on arbitrary mathematical input/indices and a contained encoded slice. FirstChecks/CountChecks/FirstGuards execute the actual zero/alignment/range/count-limit checks and expose the real allocation call; NormalEntry derives, from a genuine normal whole-function return, either the actual empty pair or a positive count,4*count=first<=slice length, count<=limit and actual allocation-call continuation. RawScalar separately proves uint32/64 bounds at every mathematical input index, without a host-window restriction. Joint success input-varlist-normal-entry-v1.log,1160 targets, permitted axioms only. Whole allocation/loop/callee ABI/record semantics/input frames and all downstream finite-certificate obligations remain open.

**Actual variable-list per-record body:** PairedScalar proves flattened dynamic add-argument uint32 reads and connects every actual loop offset load to copied bytes. VarList.StepProgram/OffsetRead extract all real step/final-store ASTs and execute their expressions. Layout derives natural row/length-cell mapping and copied-input separation from a contained slice/fresh array plan. Checks executes the actual three-way range/order predicate and signed loop/previous-index tests. StepStores/ValidStep/ValidBody execute the complete valid dynamic read/guard/two-store/two-assignment/local-scope body, preserving input even with zero body clock. FaultBody covers real SszErr23 before any store and exact lexical restoration/one call-clock payment. Unroll retains the actual evaluator clamp and all body outcomes; Walk gives exact symbolic state/clock/control/local frames for composition. Joint successful input-varlist-walk-v1.log,1283 targets, permitted axioms only. These remain conditional local summaries; whole real loop, allocation/return/ABI, record-array representation, global runtime and finite target certificate remain open.

**Whole variable-list loop and allocated tail:** AnyLoop covers arbitrary offset bytes, normal/fault outcomes, exact count normal clocks and <=count+1 including SszErr23, copied input/control and every range/order fact. Cells/IterationMemory/Filled/WalkPrevious prove actual pointer/length-cell contents through the exact walk. Return/Complete/LoopReturn execute the genuine final store/pair return and prove every record cell initialized. AllocatedTail includes both actual i/prev initialization scopes and restoration. Joint successful input-varlist-allocated-tail-v1.log,1292 targets, permitted axioms only. The array's fresh natural geometry/local binding and allocator room remain premises; actual allocator call, first-entry-to-loop/caller composition and global reachability remain to connect. Next strengthen all-outcome memory preservation outside this array before composing the allocator, then full ssz_split_var_list and fixed_list_count/gas store/global certificate.

**Variable-list allocation and whole normal caller connection:** MemoryFrame now proves and retains all-outcome preservation outside the fresh array across AnyLoop/final return/initialization scopes. Allocation executes the actual count*16 allocator, exact heap advance and complete tail, with normal count+1 and <=count+2 body clocks. NormalEntry retains exact first/count restoration; EncodedCount connects real shift2 count to raw uint32/4. BodyNormal constructs the positive fresh-array plan from a genuine nonempty normal whole-function return and proves all cells/range/order, exact clocks/globals and memory/input frames. NormalSummary covers the actual empty case too, under conservative array+4*slice_length natural room. Environment/CallerNormal include the real three-argument ABI, both tuple-return cases, caller-local restoration, resumed continuation and <=length/4+2 normal call clocks. Generic CallNormal/CallResume support arbitrary shaped values. Joint success input-varlist-caller-normal-v2.log,1301 targets, permitted axioms only. Initial runtime/code/copied-byte/arena/room and sufficient source-clock premises remain explicit; allocator-OOM/global reachability, fixed_list_count/udivmod, gas-field store, witness records and target/global finite certificate remain open.

**Payload transaction/withdrawal checkpoint (2026-10-17):** actual extra-data stores and real transaction arguments now compose through the complete variable-list caller, including empty lists, into the payload continuation. Both actual tuple-field stores and the real fixed-list counter then resume `afterWithdrawals`, with copied input preserved and at most66 fixed-list call clocks. The complete literal nonzero-divisor `udivmod` function/caller includes its early return and at-most64 loop rounds, exact source-clock payment and memory/control frames. This establishes execution bounds and return shape, not arithmetic division correctness. Actual fixed-list error guards establish zero remainder and count within limit on normal return. Successful joint closure: `input-payload-withdrawals-normal-v1.log` (1329 targets); permitted axioms only. Next: actual remaining payload stores, gas field preservation and whole payload caller; global Q/heap/gas, immutable-map equivalence, target refinement and finite K remain open.

**Actual payload gas-store checkpoint (2026-10-17):** the entire literal `decode_payload` body now checks on normal return, from copied-input/slice/runtime/allocated-room premises. This includes its minimum-length guard, allocation136, four-offset validator, extra-data guard, empty/nonempty transaction splitting, fixed withdrawal counting, all stores/returns/scopes, exact final field88=`le64(input,474)`, copied-input frame and at most `encodedExtent/4+75` body source clocks. `stored_gas_bound` connects that stored word to the original declared-gas bound using the two real fixed offsets. Successful closure: `input-payload-body-normal-v1.log` (1340 targets), permitted axioms only. Still derive allocation/runtime premises from the outer input decoder and carry the actual stored field into global guest invariants. No finite K or target certificate.

**Outer decoder stored gas / actual caller (2026-10-17):** `Request.stored_gas_from_header` now derives the completed real payload and its stored gas word bounded by200M from a normal return of the whole fixed input decoder. SI96 and payload136 allocation cursors/room connect explicitly; assumptions still include initial heap/runtime/geometry and source clock. `Payload.caller_normal` exposes the actual resumed continuation with allocated pointer, gas field, copied bytes, saved caller locals and clock bound. `evaluation_fields` transports the existing HOL-tagged canonical evaluator invariants through its field-for-field codec for all outcomes. Successful closures: `input-request-stored-gas-v1.log`1341targets and `input-payload-caller-normal-v1.log`1351targets, permitted axioms only. Audit confirmed the existing generic constructor theorem excludes the actual empty witness pointer0 through an unconditional recordsLower premise; add a separate real zero-count execution path next.

**Empty constructor / decoded witness records (2026-10-17):** the actual zero-count constructor and real scoped caller now check without any record-pointer, hash-buffer or Keccak-environment premise. This includes pointer0/count0 from the real decoder, all actual table allocation/clearing/header initialization, empty radix helper, return, caller resumption and at most44 call source clocks. Separately the entire actual `decode_bytes_list` body/caller now returns initialized concrete records, checked item-size/count limits, copied-input/earlier-heap frames and at most `2*(sliceLength/4)+3` call clocks, including the empty case. Actual `SszErr70` rejection and the complete read-only check loop are covered by local execution theorems. Successful joint closure: `input-bytes-list-caller-v1.log`1431targets; permitted axioms only. Still connect the three real witness call sites/root container and derive the global budget/target certificate.

**Actual division and withdrawal-count field (2026-10-17):** the complete real64-round `udivmod` execution now carries a natural arithmetic invariant. For a nonzero divisor<=2^63 it proves the actual quotient/remainder; the fixed-list normal body/caller also proves input divisibility. No modular-equation shortcut or extra axiom is used. Whole payload body/caller now retains the actual final field56=`(le32(input,590)-le32(input,570))/44`, with checked copied-extent count bounds; its gas-field result remains checked. Successful joint closure: `input-payload-count-field-v2.log`1386targets, permitted axioms only. Next global resource pilot: actual RLP length helpers and block-length withdrawal cap; global gas/map/heap/target obligations remain open.

## 1. What the task actually requires

The challenge asks for RISC-V bytes and a Lean proof of the fixed contract in [InitE/Challenge.lean](InitE/Challenge.lean). Lower finite K is better. The initial submission has no uniform bound: it claims infinity.

The exact declaration is `InitE.Certificate (submission : Submission) (claimed : NatE)`. Its fields require:

1. `submission.K = claimed`.
2. `submission.Admitted`, including ROM size and dispatch-layout conditions.
3. For **every** `Guest.InputBlob` whose `Guest.GasLimit.declaredGasLimit` is at most 200,000,000, if the fixed source behavior terminates with a covered outcome, a matching target execution exists within the claimed budget.

For `.finite K`, `NatE.Within` means an actual natural `steps ≤ K` and an execution of `evaluateTargetHOL` that halts with a matching result. It does not mean a benchmark estimate, a source clock bound alone, or termination at some unknown finite clock. Infinity already proves input-dependent finite termination; extracting another existential clock does not improve the score.

Important details to preserve:

- The reference is the literal `Guest.guestAst` under the pinned source semantics, not a modified microbenchmark or the optional executable testing model.
- `Guest.InputBlob` is an arbitrary finite byte list. There is **no input-length or schema-validity premise** in the certificate. The visible input arena is 128 MiB, with 16 bytes of framing, but this is not permission to assume `input.length ≤ 134217712`. Prove the behavior of larger inputs, including the length word and failed accesses, before reducing the input domain.
- The declared-gas reader follows offsets and reads missing bytes as zero. It is total and does not validate the schema. Prove how this reader constrains the gas counters actually used by each reachable execution; malformed input is a central case, not an optional test.
- Covered accepting runs must match acceptance and all 65,536 public output bytes. Covered rejections/traps need matching nonacceptance under the actual observation relation. Source resource-limit outcomes and OOM trap configurations of lengths 1, 6, and 7 are excluded. Do not exclude other failures merely because they are inconvenient. Check [InitE/Observations.lean](InitE/Observations.lean).
- The obligation is conditional on covered source termination. You need not prove termination on all inputs, but you cannot introduce extra validity/affordability assumptions without deriving them or covering the other cases.
- K counts **formal target evaluator transitions**: ordinary, foreign-call, cache, terminal, and bootstrap transitions. Crypto work inside the oracle is not charged as native instruction execution. Spike stub instructions do not map one-for-one to these transitions.
- The finite score must be strictly below `9007199254740985`; the largest allowable integer is `9007199254740984`. Prefer comfortable slack. Large displayed scores may be rounded by Yukon; Lean arithmetic must remain exact.

Read these in order: [AGENTS.md](AGENTS.md), [challenge](docs/CHALLENGE.md), [submission rules](docs/SUBMISSIONS.md), [testing](docs/TESTING.md), then the actual contract and semantics. Never read `CLAUDE.md`; the user explicitly excluded it.

## 2. What went wrong strategically, and what to change

The measurements and checked local proofs are useful. However, too much work went into making individual lemmas pass without first closing a feasible route from the exact challenge premises to a literal score. The large evidence index mainly records local facts and generated static-table checks. It does not establish global invariants, exhaustive path coverage, or a small enough numerical bound.

The older [PHASE2-PLAN.md](work/agent-notes/PHASE2-PLAN.md) is an append-only history. Its opening status and intermediate “running” entries are stale; later entries supersede them. Its old effort estimates are not promises and should not guide new spending. Use declarations, successful logs, source hashes, and the checklist above as authority.

Change the progress measure to **closed end-to-end obligations**. Before starting any subproof, answer:

1. Which exact parent theorem needs this result?
2. Which hypotheses will that parent provide, and where are they proved?
3. Does this remove a global unknown, cover a previously missing case, or materially improve the numerical budget?
4. What is the smallest check that could show the proposed connection is wrong?

If these answers are unclear, work on the interfaces or feasibility calculation first. Do not restart completed static scans, generate more per-procedure bounds indiscriminately, or polish the cheapest successful path while leaving a required failure path unbounded.

## 3. Feasibility review and the next bounded assignment

### R1. Completed review: decision and decisive arithmetic

**Decision: REVISE.** Retain weighted Named Stack accounting as a possible framework, but do not scale the existing `basic → 4*Work → 24*LabClock` recipe across the whole guest. The simple uniform compiler-multiplier route also remains unsuitable. This review has identified a specific failed budget, not established an acceptable complete replacement budget.

The inspected witness path is:

```text
main → decode_stateless_input → htr_new_payload_request → run_attempt
     → decode/hash witness headers → nodedb_build(state) → nodedb_build(code)
     → state_init → empty-transaction check → payload_header / block-size check
     → block-hash/header validation → execute_block
```

See `guest/src/main.pnk`, `guest/src/fork.pnk:923`, `guest/src/mpt.pnk:214`, and `guest/src/lib/htab.pnk:269`. These readable files guide the analysis; the final proof must concern the fixed AST/compiled artifacts. `nodedb_build` chooses a power-of-two capacity at least `2*n+2` and calls `htab_set` on each preimage's Keccak hash. Each absent-key insertion scans twice: `htab_find_slot`, then `htab_insert_raw`. This specific constructor preallocates enough capacity to avoid growth if its invariants hold; generic dynamic tables elsewhere do grow. Do not charge every witness insertion a resize, and do not assume hash probes are constant-time.

There is no schema limit smaller than the input envelope on state/code witness counts. Four offset bytes per item give the loose count ceiling `floor(B/4)`, conditional on proving the decoder/input connection. This is **not** a distinct-key ceiling that can be attained with empty items: identical empty preimages have identical keys. Keep item count, distinct keys, byte lengths, duplicate multiplicities and probe-chain lengths separate. The earlier measured 52-byte XOR-collision microbenchmark does not establish reachability of adversarial 32-byte *Keccak-derived* witness keys.

The numerical pilot inspected the fixed `Named188` (`htab_insert_raw`) loop `NamedBody188_193 = .loop NamedBody188_192`. The body has 35 syntax nodes and 2 `ticks` under the existing definitions, so `Work.basic` prices it at 37 credits. The [small parser/arithmetic script](work/agent-notes/feasibility-budget.py) recomputes this and checks the stored source hashes. This result is source inspection and exact integer arithmetic, **not a newly kernel-checked loop theorem**. It counts the basic syntax, including branches and code after early control transfer; a path-sensitive bound can improve it.

With the present `workPaid` and `padded_riscv` the extra-credit price is `37*4*24 = 3552` target steps per body. Consider the ordinary adversarial insertion allowance `P=N*(N-1)/2` occupied probes for **one** of the scans. The table below omits fixed headers in N, the other scan, final empty-slot checks, base clock, hashing, allocation, and the rest of the guest:

| Hypothetical record envelope | N from B=134,217,712 | P | `3552*P` |
|---|---:|---:|---:|
| 4-byte offsets only; loose schema envelope | 33,554,428 | 562,949,802,426,378 | 1,999,597,698,218,494,656 |
| 4-byte offset + 32-byte preimage; restricted scenario | 3,728,269 | 6,949,993,004,046 | 24,686,375,150,371,392 |
| 4-byte offset + 64-byte preimage; restricted scenario | 1,973,789 | 1,947,920,521,366 | 6,919,013,691,892,032 |

These are **conditional budget calculations**, not constructed inputs and not runtime lower bounds. In particular, the first row combines a very loose count envelope with a collision allowance without a joint realizability proof. The 36- and 68-byte rows are scenarios, not restrictions the challenge grants. Failing this upper-bound calculation means we must tighten a bound or change the approach; it does not show an input takes more than K. Even leaving room for ordinary fixed headers does not explain away the 36-byte row's factor of 2.74.

Useful exact ceilings, before unresolved overhead:

```text
Kmax = 9,007,199,254,740,984
floor((Kmax - 23,132) / 24) = 375,299,968,946,577 Lab clocks
floor((Kmax - 23,132) / 96) = 93,824,992,236,644 Work credits
```

In the 36-byte scenario, the raw scan alone can afford at most about **13.5 Work credits per occupied probe**, versus the basic rule's 37, if it consumes the *entire* remaining score. The other scan and all other work still need room. In the loose 4-byte scenario, even one Work credit per probe would exceed the cap. Therefore merely shaving the 37-credit body is not a sufficient plan for all inputs. Joint size/distinctness/multiplicity bounds and/or much more precise target pricing are needed. No cryptographic randomness, collision resistance, or average-case complexity assumption is available as an axiom.

### R2. Concrete compiler interfaces: plausible plumbing, still unproved

The source-to-Named connection is not a missing compiler *theory*: the pinned dependency exposes the relevant components. It is missing as an instantiated theorem for this challenge. The intended accounting point is **the named state `s3`, entering procedure 0**, including initialization stubs. It is **not** the earlier Stack state returned as `fullMakeInit(...).1`, and not just `main` or the list of 826 ordinary procedures.

Read these local dependency files in this order; all are under `.lake/packages/flapjack/Flapjack/`:

1. `Compiler/Backend/StackToLab/Proofs/FullMakeInitSemantics.lean`: `s3`, `s2`, `stateRel_s3`, `locToPc_start`, `stageLab`, and `assemble`. `s3` is `MakeInit.makeInit` on `StackNames.compileHOL` of the removed/allocated/raw-call program. `assemble` contains the semantic equalities across raw-call, allocation and removal; `stageLab` contains the explicit `hnames` equality across renaming. Expose these intermediate equalities in a Solver theorem, preserving their hypotheses. Do not infer an intermediate execution by reversing the final machine correctness theorem.
2. `Pancake/Proofs/PanToTarget/AssemblyWordToStack.lean`: `panToTargetWordChain`; `AssemblyLabChain.lean`: `panToTargetLabSemantics`; `AssemblyTopResource.lean`: `panToTargetInitStage` and `panToTargetLabSemanticsResource`. These expose the initial memory/code facts and the resource-limit extension. Reuse the baseline's actual stack-depth check to eliminate the allowed extra resource-limit behavior; source coverage alone does not remove a compiler-side resource-limit alternative.
3. `Compiler/Backend/StackToLab/Proofs/FlattenSemantics.lean`: `stackRuns`, `stackEntryClass`, `stackSemIsWrapper`. They give an explicit way to extract a terminating entry-call execution from the Named behavior equality, preserving events. `stackEntryClass` handles final FFI, word halt and return to `.loc 1 0`.
4. `Compiler/Backend/StackToLab/Proofs/FlattenCallCorrect.lean`: `callNoneInlCases` strips the clock tick of the artificial entry call; `flattenCallCorrect` shows how a return to the halt stub is handled. Its clock is existential, so adapt its assembly using `workPaid` rather than invoking it as a quantitative bound.

Here are the proposed interfaces, with all outstanding obligations visible. They are **design signatures**, not compiled Lean declarations. Let `L(input, installed)` be the actual initial Lab state constructed in the existing compiler proof after the 23,132-step bootstrap. Let `S(input, installed)` be its `FullMakeInitSemantics.s3`, with the fixed code/configuration and empty dynamic-code oracle. `installed` must be the machine state produced by that bootstrap, not an arbitrary state. Both states use `Guest.HostMemory` as the FFI state type and `LabToTarget.Config` as the compiler configuration type.

| Interface to implement | Required statement / explicit missing premises |
|---|---|
| **I1: Named behavior** | From exact covered source termination and actual bootstrap/installation facts, prove `StackSemEvaluate.semantics 0 S = .terminate outcome events`. Discharge fixed compilation equalities, all initialization assumptions, `mainFirst` transport, and stack/resource-limit side conditions. Then extract an entry execution and use `callNoneInlCases` to obtain the body at code lookup 0. |
| **I2: Whole-entry budget** | For that actual body `p0`, prove `BlockBound p0 EntryPre (fun _ => True) W C` for every input under the challenge gas/source/coverage premises. A precise stable entry predicate is `EntryPre st := {st with clock := 0} = {S with clock := 0}`. Prove the global invariant internally from this entry; do not leave it as an extra certificate assumption. A stronger theorem covering uncovered inputs is optional. |
| **I3: Bounded replay** | Apply `BlockBound.boundedExecution` to I1's body execution: at body clock `C+1`, retain the same result and final FFI/events, and obtain `Work p0 ... W`. Preserve the initial state except clock; prove stability of `EntryPre`. `C` is consumed body clock, not source Pancake clock. |
| **I4: Named → Lab** | Use `stateRel_s3`, `locToPc_start`, and `StateRel.stateRelClock` to pair the reclocked entry state with L. `FlattenHyps` additionally needs the actual run, non-error result, calling convention, installed flattened body and valid labels; `relCode` supplies the body-specific installation/convention facts when the relation holds. Apply `workPaid`. Handle the `.result (.loc 1 0)` case with a separately budgeted halt-stub continuation; direct `.finalFFI` and word-halt cases have terminal conclusions already. |
| **I5: Lab → actual machine** | Supply `oracleTie` and the full Lab/ASM/machine `stateRel` for the actual post-bootstrap machine, padded code and labels, at each required Lab clock. `padded_riscv` gives at most 24 times the bounded Lab clock. The logical Lab source code need not literally equal the padded target program: preserve the relation that connects them. Compose using the quantified clock shift in `BootstrapStartup.evaluator`/`TargetClock.bounded_prefix_halt`. |
| **I6: Certificate** | Carry exact terminal outcome/events or an explicitly proved matching relation through I1–I5, then use `matchingResult_refl`/oracle replay as appropriate. Change only K in the baseline submission initially, prove admission and configuration/initial-state identities, and use the same literal in the certificate and claim. |

For a whole-body bound, a conservative **proposed** arithmetic interface is

```text
LabBudget ≤ C + 1 + 4*W + H
K ≤ 23,132 + 24*(C + 1 + 4*W + H)
```

Here H is the as-yet-uninstantiated extra Lab budget for the return/halt-stub continuation and any remaining entry assembly. The procedure-0 body bound must already include compiler initialization, guest global initialization and the whole guest. H must not hide another execution of those routines. This expression has not been checked as a complete composition theorem. Match the entry-call `k-1` convention explicitly before choosing H. The previous cost factors 256, 35 and 2 are **not multiplied in again** when W and C measure the final Named program.

Assessment: these interfaces are coherent enough to justify a *small* composition pilot after the numerical gate. They are not grounds for claiming the source-to-Named bridge is done. Extracting the precise equalities from `assemble` is substantially better scoped than re-proving the whole compiler quantitatively.

### R3. First-pass work inventory and useful reductions

This is a source-level coverage audit, not an exhaustive loop proof. All rows need transfer to the fixed AST/Named execution and all word arithmetic needs range/no-wrap facts.

| Work family | Concrete finding / possible resource | Missing argument |
|---|---|---|
| Input copy and malformed input | `input_blob` checks the loaded 64-bit length against 134,217,712 before copying and calls `trap_with(8)` on excess. The host length is `BitVec.ofNat 64 input.length`. | Prove the framed-length/read relation. Lists of length ≥2^64 can wrap to a small length; do not claim every oversized mathematical list traps. Model the copied prefix and padding, including at most seven bytes read beyond the effective length. |
| Declared gas | Both first offsets are checked for equality to fixed sizes: 16 at the top container, 44 at NewPayloadRequest. Thus any path reaching a successful payload decode reads gas at blob position **474 = 2+16+44+412**. `declaredGasLimit_of_decode` already relates the pure mirror to the reader. | Prove the actual guest checks/loads imply the same bytes and that the gas field lies within the effective copied length. This narrower load/guard proof may be cheaper than full decoder equivalence. No mismatch was established in this review. |
| SSZ/payload hashing and witness headers | Variable lists have four-byte offset entries; withdrawals use 44 bytes; witness headers have count ≤256 and each ≤1024 bytes. Payload hashing happens before later block validation. | Aggregate bytes and item visits across hashing/tree construction, temporary allocation and early exceptions. Do not apply the later 8MiB RLP block check to earlier decoding/hashing or to witness data. |
| Witness tables | Two `nodedb_build` calls precede empty-transaction and block-hash checks; item lengths capped at 1024 for nodes, 65536 for code, but item count is not gas-metered. Capacity is based on *all* items, including duplicates. | Joint count/distinctness/probe/byte bounds; cost of **both** scans; later lookups; table invariants and allocation. This is the first numerical blocker. |
| User execution gas | `check_transaction` checks remaining regular and state budgets separately against the same block limit. `process_transaction` accounts regular gas before refund and state usage separately. | Global range/conservation invariant for both counters; nested forwarding, state-gas spill/refund and rollback. A local `charge_gas` lemma alone is insufficient, and a blanket 5/4 refund multiplier is not derived for this implementation. |
| System execution | `execute_block` has two unchecked calls; `process_general_purpose_requests` has four checked calls. Each uses 30M regular gas and an initial `16*97920` state reservoir. Total initial allowances: 180M and 9,400,320. | Prove those are the only invocations on this path, and account for reservoirs/credits without treating refundable state gas as a monotone counter. These numbers are not yet a total executed-work bound. |
| EVM dispatch, calls, creation, precompiles | Continuing instruction cycles need gas/rank arguments; calls can rescan code and merge child access sets. Oracle crypto internals do not cost target instructions; guest-side crypto and marshaling do. | Aggregate opcode/call counts, byte lengths and precompile work, including zero-charge exits and exceptional paths. Bound the sum of copied/scanned/cleared bytes, not arena size times every call. |
| Trie and state processing | Witness decoding uses explicit traversal stacks. The source comment says reference-side cycle guards are not modeled; do not assume a tree or cryptographic acyclicity. Persistent node allocation may provide a rank on continuing expansion. | Handle repeated references, malformed/cyclic graphs, lookups and later root recomputation. Excluded OOM outcomes do not justify omitting costly covered runs just below exhaustion. Reused frame/scratch memory does not bound cumulative work by physical arena size. |
| Withdrawals, journals and BAL | Withdrawals are unmetered by user gas. BAL sorting is merge sort in `sort_elems`, but other updates/removals, table scans and per-item encoding remain. | Stage-sensitive size bounds and aggregate journal/state/BAL work; bound deletion/back-shift and repeated scans explicitly. |
| Output and cleanup | Rejects need matching covered nonacceptance; accepting runs need all output bytes. Normal output is serialized by the fixed main routine. | Cost and result contracts for every covered handler/unwind path; exclude only outcomes excluded by `coveredOutcome`. |

The challenge gas reader is not currently the most suspicious obstruction: the fixed first-offset checks suggest a fairly direct successful-decode connection. The dominant unresolved invariant is **aggregate adversarial table/trie/state work plus gas conservation**, rather than the final memory-expansion allocator bridge.

### R4. Sol's first bounded assignment and stop conditions

Give Sol this assignment together with the whole file:

> Read the top checklist and Sections 3.R1–R4. Work only on the witness-table feasibility gate first. In one focused session (suggested cap: 60 minutes), derive a source-level joint bound in input bytes B, number of records N, distinct hashes D and multiplicities for construction and subsequent lookups. Do not assume cryptographic randomness, do not mistake the 52-byte-key microbenchmark for witness reachability, and include both scans in `htab_set`. Price the dominant scans using the actual Named/Lab/encoded loops, separating current proved prices from proposed tighter prices. Report exact arithmetic against the score cap and all remaining terms. Update this file's status and stop with go-to-next-pilot / revise / inconclusive. Do not finish more allocator lemmas, regenerate static compiler scans, or launch full builds.

Suggested order within that assignment:

1. Start with the reproduced [budget JSON](work/agent-notes/feasibility-budget.json), `Named185` (find), `Named188` (raw insertion), `Named190` (set) and the actual `memeq` callee from the [function index](work/agent-notes/guest-function-index.json). Recompute the **joint** dimension/probe allowance before building proofs. `N(N-1)/2` is a useful all-distinct collision allowance, not a bound for all repeated lookup patterns; duplicates can repeatedly query the end of a cluster.
2. Determine whether path-sensitive Work plus a more precise Lab/encoder cost suffices on paper. The existing 24 factor includes worst-case encoder and padding allowances on every line. Investigate weighted costs for the hot loops while retaining the full simulation relation; do not substitute measured Spike counts into formal target costs. Lowering one factor does not solve an oversized probe count automatically.
3. Give each unbounded remainder a symbol: at minimum input/SSZ work, witness build, later table/trie queries, gas-driven execution, system execution, cleanup/output, and startup. A proposal that allocates the whole cap to witness insertion has not passed. Recommend substantial headroom (for example a witness-build budget ≤ one quarter of Kmax); this is a planning gate, not a challenge rule.
4. Only if the arithmetic has a credible route, check **one** useful Lean pilot: a hot-loop cost/rank contract with its exact entry invariant, or the semantic bridge exposing Named `s3`. Choose whichever is the largest remaining risk. First inspect dependency availability: `Named188.olean` was absent at review time even though the broad static checks were complete. A leaf import can trigger a large fixed-proof dependency build. If the required build is expensive, record that and stop rather than importing `Solution` or weakening the invariant.

**Pass this gate** only with a defensible dominant-term budget and a named proof obligation for each remainder. It need not be a complete proof, but it must say which facts are proved, derived on paper, or still conjectured. **Inconclusive** is an acceptable bounded-session outcome. Do not label a failing upper bound a runtime counterexample. A no-go for the fixed-ROM route needs a stronger reason than this review establishes.

If the table gate cannot be made credible, possible revisions are:

- Keep the ROM, replace coarse Work/target prices with an execution-weighted cost proof and tighter aggregate data-structure bounds. This is the least disruptive candidate; the total must still fit without average-case assumptions.
- Change the implementation to a map with provable worst-case lookup bounds. This requires new ROM under Solver and a semantic refinement proof back to the fixed source, including failures; existing baseline correctness cannot simply be reused. Do not start this larger project without a new feasibility estimate.
- A watchdog that rejects after a budget can avoid bounding long **rejecting** executions only if every accepting source run is proved to finish before the cutoff and the modified code is proved equivalent before it. It does not remove the accepting-run/table problem, and arbitrarily capping witness counts can reject valid accepted inputs. Treat it as a separate proof design, not a shortcut already justified here.

After a positive table gate, check I1–I5 on one complete path before increasing local-proof volume. Then complete the other rows in R3 and obtain an overall go decision. There is still no basis for promising a short path to the final certificate on a cheaper agent.

### R5. Joint witness-table investigation, 2026-10-17: REVISE

**Result:** the Section R4 investigation is complete; the numerical gate has
not passed. The new bound separates input records, distinct hashes, duplicate
multiplicities, both scans and later queries. Much tighter proposed instruction
prices still leave the generic collision relaxation above the cap. No new Lean
theorem, changed ROM, finite claim or runtime counterexample results from this
review. The user requested the entire task; that end-to-end task remains open.

Reproduce the offline calculation and finite-model checks with:

```bash
python3 work/agent-notes/witness-table-budget.py --self-test
```

The checked output is [witness-table-budget.json](work/agent-notes/witness-table-budget.json).
The script reads fixed Named/Padded literals, records their hashes, and rechecks
all 3,834 previously indexed proof-source hashes (zero mismatches). Its arithmetic
is exact Python integer arithmetic. Its regression checks are **not** guest or
Lean verification. No cryptographic assumption or measured Spike price is used.

**Table argument, derived on paper.** Let `N` be the record count, `D` the number
of distinct 32-byte hash keys, and `m_r` the multiplicity of the key first
inserted at distinct-key ordinal `r`, with `1 ≤ r ≤ D` and `Σ m_r = N`.
Assume a valid non-full table, fixed capacity/home function, exact key equality,
no deletion, and no intervening memory corruption. Each fresh insertion before
ordinal `r` can visit at most `r−1` occupied slots in each scan. A stored key's
successful search path does not lengthen on later insertion: all slots preceding
its position were already occupied and stay occupied. Every repeat of ordinal
`r` therefore visits at most `r` occupied slots. Consequently:

```text
T = D(D−1)/2
F ≤ T + Σ_r (m_r−1)r ≤ T + (N−D)D   -- find_slot, including matching slots
R ≤ T                                -- raw insertion; repeats do not call it
F + R ≤ D(N−1)
empty-slot tests during construction = 2D
later Q lookups: occupied-slot visits ≤ QD, empty-slot tests ≤ Q
```

These are conditional mathematical bounds, not established invariants of the
fixed execution. The constructor chooses `cap ≥ 2N+2`, so if its range/table
invariants hold it cannot reach `htab_grow`: the growth condition tests twice
the new distinct count. Proving that the allocator, pointer arithmetic, used
bytes and keys satisfy those invariants remains necessary. The later-query
bound requires read-only tables; it does **not** bound `Q` by `N` or `D`.
For two witness tables, sum the per-table bounds; cross-table pairs do not probe
one another. Other dynamic tables require their own arguments.

**Joint byte constraint, derived on paper.** Distinct hash outputs have distinct
representative preimages because Keccak is deterministic. This implication
requires neither injectivity nor collision resistance. There are only
`A_k = Σ_{j=0}^k 256^j` byte strings of length at most `k`. Thus the total lengths
of representatives are at least `L(D) = Σ_{k≥0} max(0,D−A_k)`. In this input
range that is exactly:

```text
L(D) = (D−1)_+ + (D−257)_+ + (D−65793)_+ + (D−16843009)_+
4N + L(D) ≤ B
```

The four bytes per record are the SSZ offsets. The readable decoder checks
monotone offsets and forms disjoint adjacent slices. Transfer of those checks
and the effective copied-input envelope `B ≤ 134,217,712` to the fixed execution
is still unproved, including malformed/wrapped-length cases. Fixed headers and
all duplicate payload lengths are omitted, making this a relaxation. Empty
duplicates are permitted; they are never counted as new distinct preimages.
This bound says nothing about simultaneous realizability of distinct Keccak
hashes and long bucket clusters.

Distinctness is per table. The same preimage may occur in both tables, so using
`L(D_state + D_code)` would be invalid. A safe aggregate replacement is
`L₂(D) = Σ_k max(0,D−2A_k)` with `D = D_state + D_code` and `N` the combined
record count. Applying aggregate `F(N,D)`/`R(D)` further adds fictitious
cross-table probes. The JSON labels that conservative two-namespace relaxation;
it does not claim to find the actual worst split.

**Actual hot-path inspection, not kernel-checked cost.** The script follows
explicitly stipulated branches through the fixed `Padded79`, `Padded185` and
`Padded188` literals, counts non-label lines and encoded four-byte words, and
rejects unrecognized transfers. The relevant premises include aligned 32-byte
keys, the real call ABI, safe stack, valid loads/stores and the ordinary
comparison-return path. No general malformed-state execution bound is asserted.

| Cost unit | Prior checked interface / newly inspected price | Status |
|---|---|---|
| Whole raw Named body 192 | `Work.basic`: 37 credits, then `4 × 24` for extra-clock pricing only | Existing general theorem; numerical syntax inspection; no instantiated hot-loop theorem |
| Occupied raw Named path | 8 instructions, 3 skips, 1 tick, 1 continue, 1 conditional; proposed Work15 using selected branches/sequences | Source inspection; needs all-clock/control-transfer proof |
| Occupied raw Padded path | 10 non-label lines, each one encoded instruction, at label `188.10` | Literal path; no target evaluator/state-relation proof |
| Aligned 32-byte memeq | 17/20/23/26 instructions for first mismatch in word 0/1/2/3; 26 for equality | Literal stipulated paths through `Padded79` |
| Occupied find mismatch | 60 caller non-label lines plus 26 callee lines; three extra encoded words (`longMul`, two `locValue`); total **89** | Literal path; safe-stack and return premises unproved |
| Occupied find match | Corresponding total **83** | Literal path; using 89 for all visits is conservative |

Each encoded ordinary instruction should consume one target evaluator transition
only after the relevant fetch, interference, cache/dispatch and machine-state
premises are supplied. These prices do **not** follow from `padded_riscv` just by
substituting a smaller coefficient. A replacement weighted simulation retaining
its full relation is needed. The proposed Work15 still pays **1,440 extra target
steps per probe** through the existing `4 × 24` route, excluding base clock.

**Exact arithmetic.** The script maximizes each stated dimension relaxation by
splitting at the preimage-length thresholds and `D mod 4`; within each piece
the weighted objective is quadratic. Independent brute-force searches validate
the optimizer for small alphabets/budgets, including every tier used there.
`B` below is the full effective input bound with headers omitted.

| One-table relaxation at B=134,217,712 | N | D | Occupied term |
|---|---:|---:|---:|
| Maximize `F+R`, price one per visit | 18,890,847 | 18,890,846 | 356,864,062,595,716 visits |
| Maximize old raw-only extra-clock price `3552R` | 18,890,847 | 18,890,846 | 633,790,541,619,849,120 target steps |
| Maximize proposed raw-only extra-clock price `1440R` | 18,890,847 | 18,890,846 | 256,942,111,467,506,400 target steps |
| Maximize proposed literal-path price `89F+10R` | 23,025,715 | 14,060,301 | **21,004,777,811,675,496** proposed target steps |

In the last row `F=224,902,444,504,764` and `R=98,846,025,075,150`.
Repeated queries make the weighted optimum occur with fewer distinct keys and
many duplicates. A duplicate's final matching comparison saves six instructions
relative to 89; that refinement is linear in `N−D` and cannot explain this
quadratic budget excess. The two-namespace aggregate `89F+10R` allowance is
21,025,446,398,591,943. Neither value is a reachable execution lower bound.

At the maximum one-table combined-visit allowance, the entire cap minus startup
can afford only 25 target transitions per occupied visit on average. A quarter
of the cap affords six. The existing Work route fails by much more; even the
new proposed literal price fails by about 2.33 times the full cap. Therefore
the generic size/distinctness bound plus these path prices does **not** pass
the witness gate. This does not rule out a sharper aggregate comparison/bucket
bound for the actual hash family, or an alternative target implementation.

Keep the missing total explicit:

```text
K ≤ startup + input/SSZ + witness_build + later_queries/trie
            + user_gas_work + six_system_calls + other_tables/journals
            + failure/unwind/cleanup/output + compiler_entry/return_overhead
```

Only the conditional 23,132-step startup theorem is numerically settled here.
`Q`, the later-query aggregate and the other global work/clock terms remain
unknown. There is no numerical margin or overall go decision.

**Concrete revised obligation.** For the unchanged ROM, a sufficient next
result would bound the aggregate weighted probe/comparison-prefix work of
Keccak-derived keys, including duplicates and later reads, under actual input
and guest invariants. A small average-load assertion or a probe-body rank alone
does not supply that result. Without it, do not fund another round of the same
coarse local contracts.

An implementation alternative can be scoped to the two read-only witness maps:
`nodedb_build` has two callers; `nodedb_lookup` is their lookup interface, with
two trie call sites and one code-state call site. A stable radix-sorted index
on 32-byte hashes could make construction linear in `32N` and lookup logarithmic
in `D`, with the last duplicate record winning. This is a **design**, not an
implemented or proved replacement. It requires a new ROM, extensional map
refinement, allocation/separation and covered failure/observation proofs, new
compiler artifacts and a whole-program budget. Every public output byte must
still match on accepting runs, and new memory exhaustion cannot replace a
covered source success. No permission-dependent external step is blocking this work;
the missing mathematical/refinement argument is the blocker.

**Validation and stop condition.** The script passed 186,368 exhaustive small
table executions, 2,050,048 subsequent lookups (including absent keys and wrap),
and 1,616 comparisons with an independent brute-force optimizer. The successful
guarded run is `logs/witness-table-review-v3.{log,time}` with matching resource
JSONL. No Lean pilot was launched: the arithmetic gate failed, and the selected
fixed `Named79/185/188/190.olean` dependencies are absent. The incremental policy
check also passed; it is not a trusted audit or isolated verification. Keep the
live claim at infinity and retain the unfinished certificate checklist above.

### R6. Active radix implementation and proof chain (2026-10-17)

The user explicitly authorized changing the plan and removed the old stop
points. The algorithm is now implemented as proposed replacement declarations
under `Solver/WitnessRadix/RawProgram.lean`, with their insertion into the fixed
declaration list defined in `Program.lean`. `Guest.guestAst` and the live
`submission/Solution.lean` remain unchanged. This is active development toward
the finite certificate, not a completed solution or a new pause/review gate.

The index uses stable partitions over the 256 hash bits, compresses unary
levels, and selects the final input ordinal when all remaining hashes agree.
It requires no cryptographic distribution or injectivity assumption. The
Pancake implementation uses an explicit worklist and has no recursive call.
All pending tasks describe disjoint remaining index intervals. New hashes,
branches and tasks stay inside the original `htab_new` allocations:

| Original allocation | Proposed contents |
|---|---|
| keys, `32*cap` bytes | N 32-byte hashes followed by 24-byte branch records |
| vals, `8*cap` bytes | N slice-record pointers, then pending-node pointers |
| order, `8*cap` bytes | N active ordinals, then pending-right starts |
| order_pos, `8*cap` bytes | N partition ordinals, then pending-right counts |
| used, cap bytes | Original zeroed allocation retained |

The header count word becomes the index root. Odd roots encode leaf ordinals,
even nonzero roots point to aligned branch records, and zero means empty.
The unchanged opaque interface is `nodedb_build`/`nodedb_lookup`; callers still
receive original slice pointers/lengths. The constructor hashes in original
input order through the existing scratch buffer and retains the original
allocation sequence and capacities. None of these design facts substitutes for
the remaining memory/refinement proof.

Checked chain so far:

1. `Model.lookup_build` proves generic stable construction equals a last-wins
   dictionary, including all duplicates and absent queries. `height_build`,
   `leaves_build`, and `buildVisits_bound` give abstract structural bounds.
2. `Compact.hash_lookup` proves the final single-record leaves preserve that
   dictionary for actual `BitVec 256` keys. `hash_query_visits` proves at most
   257 inspected index nodes for every query.
3. `Space.branches_buildIndex` proves at most N branches;
   `buildIndex_key_pool_fits` fits hashes/branches into the original key area
   when `cap ≥ 2N+2`. `Addressing` proves no-wrap address conversion and
   non-aliasing of hash/branch words and data/pending array cells, under explicit
   allocation/range/alignment premises.
4. `Scatter.scatter_eq_blocks` proves the stable scatter's exact output and
   complete unchanged-memory footprint. Its premise uses the **actual zero
   partition length**, allowing adjacent zero/one output intervals as in the
   implementation. This improves the first version's over-strong N-sized gap.
5. `Visits.hash_array_passes` accounts for three passes at every level (count,
   scatter, copy back), conservatively including passes skipped by unary
   levels. The bound is **769N record-pass visits**, or 25,803,355,132 when
   `N ≤ 33,554,428`. `hash_query_total` bounds Q queries by 257Q inspected
   nodes. These units are not target transitions; terminal key comparison,
   hash/copy/setup work and real instruction pricing remain to be composed.
6. `Program.nonFunctions_preserved` proves the scalar globals, structs and
   exception declarations are literally unchanged; the two ABI theorems prove
   function names, parameter lists and result shapes match the original.
   `QueryEmpty.empty_table` proves an execution of the **actual new lookup
   HOL AST** at an empty root for every clock, preserving memory, FFI and clock,
   from a real local `db` binding, mapped root cell and zero root word.

7. `ByteKeys` instantiates lookup on actual 32-byte arrays. `WordBits` proves
   the candidate's 64-bit shift/mask expression selects exactly the modeled
   bit, and proves nonzero/odd/decoding facts for leaf tags without wrapping.
   `Graph.lookup_represents` follows those tag/child/record addresses and
   proves the read-only traversal returns the dictionary result within 257
   inspections, **conditional on an encoded-tree representation**. Constructing
   that representation and lifting this traversal to actual HOL remain open.
8. `Worklist` proves logical iterative termination within 257N tasks, record
   mass never increases, and at most N current/pending task slots. Identifying
   those tasks with the actual parallel arrays remains open.
9. `Input.Framing` proves actual initial host-memory bytes and length framing
   for arbitrary input-list lengths, including 64-bit length reduction.
   `Input.HostGas` connects the challenge reader to host bytes 474..481 and
   the 64-bit gas word under the two fixed-offset checks. Actual decoder
   execution and host-to-guest copying must establish those premises.

10. `QueryBranchStep.branch_iteration` proves a complete branch iteration of
    the actual candidate lookup HOL AST updates only `node`; bit/digit locals
    are restored and all other state fields, including memory/FFI/clock,
    remain identical. Premises identify actual word/byte loads and the selected
    mapped child. The outer while consumes its separate clock.
11. `Memeq32Memory.aligned_memory` proves the whole fixed-source `memeq` 32-byte
    aligned path from actual argument bindings, alignment mask and eight
    mapped-word loads, including every early mismatch. Its Boolean result is
    equality of the four words' 32 little-endian bytes. `WordKeys` checks that
    byte equality iff word equality. Source-to-memory byte correspondence,
    the unaligned loop path and the lookup call/return composition remain open.
    `ComparePrefix.execute_prefix` handles arbitrary early-mismatch test
    sequences and is the next ingredient for that unaligned path.

The successful logs include `witness-radix-space-v1`, `scatter-v2`, `visits-v1`,
`addressing-v1`, `program-v3`, `query-empty-v5`, `graph-v3`,
`memeq32-memory-v4`, and `compare-prefix-v1`. The main printed declarations
use only permitted axioms; the proposed literal routines use none. Earlier
failed attempts are retained and not indexed as proof evidence. In particular,
do not use failed-log `sorryAx` prints. No explicit proof holes were added.
The broad `rfl` attempt on a well-founded source codec failed; rewriting its
equations establishes the actual AST shape without whole-term reduction.

Development execution evidence (not formal evaluator verification): the pinned
compiler produced a linked 954,448-byte ROM image at
`work/agent-notes/witness-radix-candidate.elf`. Sixteen accepting EEST records
pass, and every one of their 65,536 public output bytes matches the baseline
under Spike. A separate compiled unit calls the actual routines on empty,
singleton, duplicate, long-common-prefix and repeated-key inputs; all passed.
The full candidate run completed: **33,614 records, 33,605 PASS(full),
9 PASS(malformed), no failures**, in `logs/witness-radix-eest-full-v1.log`
and its JSON. The remaining stepped-interpreter regression cases also passed
with guard 10,000 (`logs/witness-radix-executable-v4.log`, exit 0). Its earlier
large-guard run was terminated without a result; v3 passed four initial cases
then exhausted an overly small 1,000-iteration guard on duplicate buckets. The native/stepped models do not certify the HOL
source/target contract.

The new compilation changes startup metadata: its bitmap buffer endpoint is
`0xa0029050`, code-buffer begin `0x800de2f4`, and code-buffer end `0x800df000`,
versus fixed source values `0xa0029048`, `0x800ddd94`, `0x800de000`.
**Do not reuse baseline installation or the 23,132-step startup theorem as if
those premises still held.** The source/map refinement must include the initial
reserved-page relation or establish the required observation-preserving
independence; new artifact, installation and bootstrap facts must be checked.
The additional data word suggests five extra copy-loop steps, but no new
bootstrap-clock theorem is claimed.

Continue on these concrete obligations:

- Connect the actual iterative worklist, stable buffers and encoded branch
  graph to `buildIndex`, including unary levels and final duplicate selection.
- Prove all nonempty lookup paths under the encoded-graph/memory invariant,
  including unaligned query bytes and the original memeq call/return.
- Prove the fixed guest's original witness construction satisfies the same
  last-wins map abstraction, and establish private-memory ownership across
  every caller. Close the startup-header issue above in this relation.
- Check new compiler/ROM/dispatch/installation artifacts; price actual loop
  execution through full compiler state/oracle relations.
- Derive input framing/gas correspondence and whole-guest Q, gas, allocation,
  trie/journal/cleanup bounds. Compose a literal total below the score cap,
  then the real certificate and permitted final verification.

### R7. Global resource pilot after decoded-record/gas connections (2026-10-17)

Decision: **inconclusive; no whole-program go or finite K**. Keep resolving the
resource premises. Local input/caller proofs above remain useful evidence, but
are not a substitute for this gate.

Offline `work/agent-notes/global-resource-pilot.py --self-test` records exact
source hashes and checks its integer quadratic optimizer against2160 exhaustive
small scenarios (`global-resource-pilot.json`). This is arithmetic bookkeeping,
not a runtime bound or a constructed attack. It jointly constrains first-touch
count D and subsequent warm-query count W by `cold*D+100*W<=G`, then maximizes a
stated triangular-construction plus `D*W` probe relaxation. The actual cold
account constant is3000; cold storage is2100. A380M gas scenario (200M user plus
six30M system allowances) is **not a proved executed-gas total**, due to refunds,
state reservoirs and forwarding/rollback. For a single storage-map dimension
model it gives176,097,514,634 occupied visits at D=92,683,W=1,853,657. Map
multiplicities, rehash/delete/copy work and phase sharing remain unproved. Do not
sum full-G scenarios as if they were one established global budget.

Useful source observations, still requiring actual-execution proofs:

- `block_rlp_length` is checked against8,388,608 before content tries and before
  `process_withdrawals`. `withdrawal_rlp_len` has a fixed21-byte address term,
  three positive integer lengths and a positive list header. Actual small-
  divisor arithmetic, no-wrap length accumulation, whole header/block callers
  and the literal guard now check: under their decoded-data/layout/code/clock
  entry premises, successful continuation implies withdrawal count<=335,544
  (`input-block-guard-v3.log`). Deriving those premises from the complete root
  builder remains open. Earlier SSZ hashing still permits the larger copied-
  input extent. These are different phases.
- Mutable `htab_del` uses one backward-shift scan; it does not call raw insertion
  once per shifted entry. Collision accounting must include its copies/hashes,
  but a quadratic reinsertion cost per deletion would misread the code.
- Later warm lookups may hit a deep preexisting withdrawal-grown account map.
  A single-map120M post-withdrawal scenario with335,544 free preexisting keys
  gives402,652,800,000 occupied visits, before operation multiplicities. This is
  not charged to cold gas already spent in that later window.
- The persistent arena has31,092,374,808 bytes. Pairing a nonterminal immutable-db
  query with32 persistent allocated bytes would permit971,636,712 such queries,
  plus separately bounded root/last-failure queries. This pairing is **not yet
  a theorem**. `_decode_step` allocates RLP slice arrays and rejects empty
  extension paths; `_decode_witness_node` restores scratch rather than heap.
  `ws_storage_trie` decodes before its caller's temporary key-hash heap scope.
  Do not assume cryptographic acyclicity or that physical scratch bounds
  cumulative work. Scoped indexed-trie builders need their own aggregate bound.

Actual gas-local checkpoint: `GasBudget.Refill` and `Refund` execute the fixed
routines and all scopes, retaining exact memory/clock/control frames. Their
real ignored callers also check. Under readable frame/message cells, runtime
code, clock affordability and `gas_left+spill<2^64`, the natural sum
`gas_left+regular_gas_used+outstanding_spill` is preserved. The spill cell is
frame offset192, regular-used184, liquid64 and state-left72. Refill reservoir
read separation is explicit. This rules out treating these local reservoir
restorations as fresh regular budget. It does not cover the whole call tree or
prove a380M total. CALL/CALLCODE subtract forwarded gas including the2300
stipend from regular-used; nonzero-value overhead11300 must pay for that credit.
Current intrinsic cost returns `<regular,0,floor>` and the block regular counter
is computed before ordinary transaction refund subtraction. The actual
charge_state_gas affordable reservoir/spill paths and unaffordable exception
now check, including add_sat exact branch, all stores/scopes and real ignored
callers (`gas-state-charge-call-v1.log`). Under state_left+gas_left<2^64 and
regular liquid+spill<2^64, successful calls preserve the same natural regular
budget; failures raise before any pool write. Body costs<=1, callers<=2 source
clocks. These no-wrap/entry facts remain global invariant obligations. Signed state-use
and pre/post child transfers still need actual no-wrap and conservation proofs.
The complete actual calculate_message_call_gas body/caller is checked in its
zero-memory/extra-cost mode; all four literal opcode call sites supply those
arguments. The exact charge/used-counter-debit prefix is also checked and
identified in all four opcode ASTs. Under funded stipend and no-wrap entry
premises, resulting parent budget + forwarded child seed equals prior parent
budget (`gas-forward-sites-v6.log`). The natural counter identity accounts for
stipend credits, so they are not treated as fresh gas. Proving actual up-front
fee funding, successful child handling and root/block accounting remains open.
`global-resource-pilot.py` hashes evm_calls/tx too and records checked local
results while leaving all whole-run/target flags false.

Next quantitative pilot: close the joint gas/table resource invariants and
persistent-query allocation pairing. Actual small-divisor arithmetic/count
bounds and the whole block-call/withdrawal-guard connection are now checked,
with root entry/clock/layout obligations still explicit. The complete mutable operation multiplicities and final weighted
compiler/target pricing remain major open obligations. No new algorithmic
impossibility or reachable runtime counterexample was established by this audit.

### Review protocol for subsequent sessions

Recommended initial spending limit: one focused review session, roughly 60–90 minutes, plus at most three small targeted builds if needed. This is a planning limit, not permission to run expensive jobs. If the review remains inconclusive, record exactly why; do not turn it silently into another multi-hour proof campaign.

### Gate A — verify the checkpoint without rebuilding it

- Check Git branch/status, claim, toolchain, available RAM/disk, and actual process state.
- Read the top checklist and the latest progress entries. Verify indexed source hashes if the checkout has changed. Inspect the final successful logs rather than rebuilding thousands of modules to confirm known results.
- Read the statements of the proposed connection lemmas. List every parameter and hypothesis, including error exclusions, clock equalities, memory relations, installed-code equalities, stack bounds, compiler-oracle restrictions, and FFI assertions.
- Keep a small obligation table with columns: **goal / prerequisite / evidence / missing fact / chosen next action**. A statement that assumes the desired bound does not discharge that bound.

**Output:** an accurate map of what can actually be applied, not just theorem names that sound relevant.

### Gate B — choose the accounting layer and close the interface design

The most recent work measures the fixed, named **Stack** program using `FlattenWeighted.Work` and `BlockBound`. That is a different strategy from bounding a Pancake clock and multiplying every uniform compiler factor.

Compare these routes explicitly:

| Route | Why consider it | What must be supplied |
|---|---|---|
| Weighted work on the fixed Named Stack program | Reuses recent guest summaries and avoids charging the largest procedure on every iteration | Source-to-this-exact-stage execution/initial-state connection; global Stack invariant and total work/clock bound; flattening and Lab/target connection |
| Earlier-language potential transported quantitatively | Source structure may make gas and parsing invariants easier to express | A useful work measure and preservation through every relevant optimization/lowering pass, with numerical factors that fit |
| Direct Lab/RISC-V potential | Could avoid some compiler budget inflation | Low-level state invariants, complete dispatch/FFI handling, and coverage of every required path; this is a new proof burden, not a free shortcut |

For the preferred route, write concrete theorem signatures for every arrow in Section 4. Use named hypotheses for unproved interfaces; do not add permanent axioms or present assumptions as results. A small parametric composition theorem is useful if it exposes all missing premises. It is **not** the final certificate.

Check especially whether an existing source compiler theorem supplies an execution at the precise Named Stack stage. A theorem about final behavior does not automatically let you recover an intermediate execution by running the compiler proof backwards. Identify the forward simulation and initial relation you will use.

**Output:** one selected route, explicit missing bridges, and reasons for rejecting or retaining alternatives. If no coherent interfaces can be stated, do not continue bulk local proof work.

### Gate C — inventory adversarial work and potential resources

Inspect the actual reachable guest code and its loops/calls. For each component record a bound on its iteration count, cost per iteration, resource that pays for it, and the proof needed for that resource bound. Start with likely worst cases, not easy opcodes:

- Parsing, offset arithmetic, payload copying/hashing, and malformed/oversized inputs.
- State/witness ingestion, hash collisions, resizing, deletion, and rollback. Hashing is deterministic; average-case hash-table complexity is not a valid adversarial bound.
- Header/transaction/withdrawal counts and system calls with independent gas pools. Do not assume a single input's declared gas bounds the sum of every internal budget or every item in a collection.
- Repeated code scanning/jump-destination construction, calls, CREATE, frame allocation/release, and return-data copying. The 63/64 forwarding rule bounds some nesting behavior; it does not alone bound the total number of sequential calls or rescans.
- Gas refunds, forwarding/return, failed charges, stipends where applicable, and memory expansion. A local positive-charge lemma does not prove all continuing paths consume positive gas.
- Cryptographic/precompile paths as actually implemented in this fixed program: distinguish software guest work from oracle work.
- Exceptions, runtime unwind, journal cleanup, output, and initialization. Check covered trap cases individually.

Build a proposed vector potential, for example: remaining actual gas in all relevant pools, remaining input items/bytes, unprocessed table entries, probe budget, journal work, frame/continuation work, and one-time initialization. This is only a design suggestion. Derive the real components from the code. Explain how calls/refunds move potential without creating unbounded budget.

Give gas-reader correspondence particular attention: try to identify whether malformed offsets or multiple payload items could make the challenge reader report a small number while the actual guest executes a different, much larger budget. This is a question to investigate, not an asserted counterexample. If possible, determine whether the resulting source termination is covered. A mismatch here could invalidate the intended gas-based potential before any local arithmetic proof matters.

For bitvector counters, prove no-wrap/range facts before using natural-number subtraction, addition, or strict decrease. Finite address width does not by itself yield a useful execution bound.

**Output:** a coverage table with no silently omitted work. Unknown rows remain unknown, not zero. A required positive-cost cycle with no resource/rank argument is a feasibility failure until resolved.

### Gate D — perform exact budget arithmetic before scaling proofs

Keep units separate: gas, bytes, input items, source clock, Stack Work credits, Lab clock, target transitions. For each coefficient record its source and status: **checked**, **proved on paper but not formalized**, **measured example**, or **guess**. Only the first category is certificate evidence.

The previous uniform route has a concrete warning:

```text
24 * (4 * 12091 + 5) * 2 * 35 * 256 = 20,802,539,520
floor(9,007,199,254,740,984 / 20,802,539,520) = 432,985
```

These are conditional accounting calculations, not a whole-program theorem. They leave fewer than 433,000 source clock units before additive costs. The uniform 12,091-node maximum comes from a large initializer; charging it repeatedly is the problem. The previous Lab factor 402 was tightened to 24, but that alone did not rescue this approach. Do not repeat the uniform route unless you can justify a source bound that actually fits.

For a weighted route, investigate a formula of the following **schematic** form:

```text
K ≤ 23,132 + 24 * (bounded initial Lab clock + 4 * total Stack Work + entry overhead)
```

The `4 * Work` is an upper bound on flattening's **extra** clock, not the whole Lab clock. The baseline clock must also be bounded. Check the precise entry, halt, stubs, and state-relation terms before asserting this formula; it has not been assembled as a theorem. Do not multiply Crep/Word factors into already-computed Named Stack Work without a derivation; that can double-count costs.

Use a small exact-integer Python calculation for proposed totals. It is bookkeeping, not proof. Evaluate worst allowed dimensions, including products/quadratic terms. Compare both plausible and conservative bounds to the score cap. If a dominant term exhausts the cap, identify which bound must tighten and whether that is structurally plausible. Measurements may refute an estimate for an actual measured case; they never prove a universal upper bound.

**Output:** a budget table, the total or an explicit list of unknown terms, and margin to the cap. Do not fill unknowns with the old guessed envelope.

### Gate E — pick pilots that could invalidate the plan

Choose at most three targeted pilots from the largest gaps. Good examples:

1. A thin compiler/initial-state composition interface at the chosen accounting layer, with each global budget hypothesis visible.
2. The relationship between the challenge's declared-gas reader and all reachable gas pools, including malformed input and multiple items.
3. A genuinely adversarial unmetered loop family, such as collision-chain construction, with a size bound derived from input/allocation facts rather than an assumed per-call maximum.

Choose based on the coverage/budget table, not this list's order. Completing another memzero detail is a poor feasibility pilot unless that detail is the identified bottleneck.

**Decision:** proceed only when the interfaces are coherent, no required work category is ignored, and the numerical route is credible. “Go” does not mean the proof is done. If inconclusive or no-go, write the evidence and propose a specific alternative; do not keep generating the same class of local facts. Do not change ROM or dependencies merely to make existing tests pass.

Maintain this decision record after each review (current review: Sections R1–R4 above):

| Review item | Current answer | Evidence needed to change it |
|---|---|---|
| Decision | **REVISE; coarse witness budget fails; overall feasibility unresolved** | Joint table-work budget, then instantiated interfaces and remaining coverage/budget rows |
| Preferred route | Named `s3`, procedure 0, with tighter hot-path accounting if affordable | Existing semantic stages exposed as I1; a successful numerical gate and a manageable global invariant |
| Uniform total Stack Work bound | Unknown; naive raw-probe pricing already too large | Joint data-structure bounds and/or improved execution-weighted costs; no average-case assumptions |
| Uniform replay/base clock bound | Unknown | Whole-entry clock/rank argument, including failure/unwind paths |
| Final composed target coefficient/additive terms | Individual 4, 24 and 23,132 facts exist; `C+1+4W+H` assembly is unproved | I1–I5, including halt-stub H, actual code, state and oracle relations |
| Numerical margin to score cap | No credible total; the 36-byte raw-scan scenario alone prices at 2.74 times Kmax | Exact revised total with all dominant terms budgeted |
| Next review result to report | Witness construction and later-query budget, or a precise unresolved obstacle | Bounded Sol assignment in R4; do not proceed automatically to local allocation proofs |

Do not treat finite memory, classical choice, or finiteness of a reduced input set as an escape hatch. Even if they give existence of a maximum, the task still needs a concrete bound below the score cap; the required finite-state/input reduction itself must also be proved.

## 4. End-to-end proof outline and acceptance criteria

The following is the intended chain, **not an existing completed proof**.

### A. Keep the baseline bytes and make the score change explicit

Initially prefer the existing ROM/configuration. A candidate can be the baseline submission with only `K` replaced by `.finite K`. In [SubmissionModel](InitE/SubmissionModel.lean), `machineConfig` and `initialState` do not use K. Prove the required equalities and transport admission rather than assuming changing `claimedScore` alone is sufficient. If code/configuration changes, existing bootstrap and correctness premises must be reconsidered.

**Done when:** the eventual candidate's score, admission, code, configuration, and initial-state identities are proved. Keep the live submission at infinity until the actual finite proof exists.

### B. Obtain a relevant execution from the exact source premises

Start from the certificate's input, gas, source termination, and coverage hypotheses. Use forward compiler semantics to obtain a non-error, non-timeout execution of the exact program at the chosen stage, preserving enough FFI/result information to finish matching. Identify its code, compiler oracle, memory layout, stack conventions, and initialization relation.

For the current weighted route, identify the fixed Named Stack entry and its installed code, including generated runtime stubs. Do not assume proving 826 ordinary procedure facts covers every stub or oracle-generated body.

Some local bounds include malformed states that stop with a Stack evaluator error. That is useful for local cost accounting, but compiler simulation theorems can require a non-error execution. The forward connection must establish the required non-error fact for covered source runs; a cheap bound on an erroneous intermediate execution is not a matching target execution.

**Done when:** an actual applicable theorem yields the needed execution and initial invariant. An unbounded execution is acceptable at this stage if the next stage bounds it without circular assumptions.

### C. Bound/compress the guest execution

Prove the global invariant and potential from Section 3. The desired interface must provide both:

- a uniform bound on the relevant initial/replay Stack clock;
- a `Work` derivation with a uniform total credit bound for the corresponding execution.

`BlockBound.boundedExecution` can replace an existing non-timeout execution with one at `clocks + 1`, preserving the result and every final-state field except unused clock, provided the entry predicate is stable under changing the clock. Its normal postcondition concerns only `(none, next)` fall-through; returning results and exceptions require their own summaries.

Local success/affordability/arena premises must follow from the invariant, or the other paths must have their own bounds. Do not assume a memzero length is at most the full arena at every call and multiply that by every possible call without checking the resulting total. Prefer aggregate charging of actual lengths where possible.

**Done when:** a whole-entry theorem, under only derived initialization facts, bounds every execution needed by the challenge. No “all callees bounded,” “all loops terminate within N,” or “total work ≤ W” hypothesis may remain unexplained.

### D. Transport to the actual Lab and target evaluator

Apply `FlattenWeighted.workPaid` to obtain flattening's additional clock bound and original simulation conclusion. Discharge all `FlattenHyps`, entry/return/label, code-installation, and state relations. Include the bounded base clock.

Apply `LabBoundTight.padded_riscv` to the actual padded layout. It yields the factor 24 under its original relation, no-install/static code, successful execution, and oracle premises. Preserve the complete FFI state and result; a number-only inequality is insufficient.

Compose `BootstrapStartup.evaluator`'s 23,132-step prefix from the challenge initial state with the bounded body execution. Check whether terminal/entry overhead is already included before adding or omitting a step. Use the actual evaluator composition lemmas, not an analogy to Spike.

**Done when:** an execution of `evaluateTargetHOL` from the candidate's actual `initialState input` halts within the numerical bound, with the data needed for `matchingResult`.

### E. Finish observation matching and the certificate

Reuse the existing behavior correctness and oracle replay results where applicable, or preserve the relevant result/FFI equalities through the quantitative chain. Prove accepting output equality and the required rejecting relation. Do not infer matching solely from “both halt.”

The packaging target, written schematically, is:

```lean
-- Schematic interface only; this is not a checked declaration in this file.
uniform_matching :
  ∀ input, Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
  ∀ outcome events,
    InitE.sourceBehaviour input = .terminate outcome events →
    InitE.coveredOutcome outcome →
    ∃ steps, steps ≤ K ∧
      InitE.matchingExecutionAt candidate input outcome events steps
```

Together with score equality and admission, this supplies `InitE.Certificate candidate (.finite K)` by unfolding the finite `NatE.Within` contract. The difficult work is proving `uniform_matching`, not writing this wrapper.

**Done when:** the real `submission/Solution.lean` theorem is checked against the fixed contract, its axioms are permitted, and `claim.json` matches the same literal K. Official verification is a further, separate gate.

## 5. Reusable proof inventory: read statements before applying

All paths in this section are under `submission/InitECandidate/Solver/` unless shown otherwise. The evidence manifest records hashes and printed facts; a successful local build is not isolated comparator verification.

| Area | Entry points | What exists / what remains |
|---|---|---|
| Startup | `BootstrapStartup.lean`, `BootstrapEncoding.lean`, `TargetClock.lean` | Exact 23,132-step prefix; baseline code/configuration premises remain explicit. |
| Crep → Loop | `CrepToLoopBound/Entry.lean`, `CrepStatic/Fixed.lean` | Fixed ceiling 126; conditional entry clock multiplier 256. Initial code/state/memory/global relations must be supplied. |
| Word → Stack | `WordToStackBound/CompileEntry.lean`, `WordStatic/Fixed.lean` | Fixed ceiling 17; conditional entry multiplier 35. Initialization, conventions, compiler oracle, bitmaps, and stack-space hypotheses remain significant. |
| Other passes | `WordToWordBound/Entry.lean`, `StackRawCallBound/Entry.lean`, `StackAllocBound/Entry.lean`, `StackRemoveDirect/Entry.lean`, `StackStatic/Fixed.lean` | Checked conditional simulations/static eligibility. RawCall factor 2, Alloc no extra clock, restricted RemoveDirect accounting; do not silently generalize restrictions. |
| Weighted flattening | `FlattenWeighted/Work.lean`, `Common.lean`, `BlockBound.lean`, `BlockReclock.lean`, `BlockPrefix.lean`, `BlockSelected.lean` | `Work` is an inductive source derivation; `workPaid` bounds extra target clock by 4 credits each. `BlockBound` tracks work, clock consumption, normal postcondition, and timeout-zero behavior. |
| Loop machinery | `FlattenWeighted/` rank/loop modules | Generic rank and invariant interfaces exist; each actual loop still needs a valid rank, preservation, and body budget. |
| Lab → target | `LabBoundTight.lean`, `LabBoundTight/PaddedRiscV.lean`, `LabBound/Layout.lean` | Complete fixed 832-section layout; line ceiling 24 bytes, encoder ceiling 16, final multiplier 24. Original state/oracle/execution hypotheses still apply. |
| Memzero | `GuestWork/MemzeroLinear.lean`, `MemzeroMemory.lean`, `MemzeroFrame.lean`, `MemzeroCall.lean` | Whole Named78 body: Work ≤ 17·length+447, consumed clock ≤ length+43 under the stated entry/range facts. Separate memory/register effects and real-call bounds exist. |
| Allocation | `GuestWork/FrameAllocAllClocks.lean`, `FrameAllocBlock.lean`, `FrameAllocState.lean`, `FrameAllocCall.lean`, `FrameArena.lean` | Whole guarded Named71 allocator: Work58/clock4 for every initial clock; actual call134+return continuation: Work82/clock5. Allocation guards and ABI facts are premises, not global results. |
| Gas | `GuestWork/GasAccounting.lean`, `ChargeGasEntry.lean`, `ChargeGasCost.lean` | Affordable Named472 charge conserves gas-left+used without wrap, Work49/clock2. Does not prove global gas conservation, positive charging on every path, or out-of-gas unwind bounds. |

Specific memory-expansion milestones:

- `GuestWork/ExtendMemoryZero.lean`: complete Named484 routine at zero expansion; Work21, consumed clock1, replay clock2. Word stack/metadata registers suffice; safe stack, valid memory, installed memzero, and valid return location are not required for this bound.
- `ExtendMemoryEntry.lean`: complete nonzero no-growth case; Work `17*M+569`, consumed clock `M+50`, replay `M+51`. `Ready` includes entry ABI, safe stack, concrete lookup domains/values, capacity comparison, and amount ≤ M.
- `ExtendMemoryNoGrowth.lean`: branch264/suffix364; Work `17*M+534`, clock `M+47`.
- `ExtendMemoryLength.lean`: final suffix363, including pointer lookup; Work `17*M+527`, clock `M+46`. Invalid lookups stop early. Installed callee and bounded length still matter.
- `ExtendMemoryBlock.lean`, `ExtendMemorySetup.lean`, `ExtendMemoryTransfer.lean`: capacity-clearing call setup, call, restore, and capacity store with saved-length transfer.
- `ExtendMemoryCapacityEntry.lean`: actual suffix248 after allocator return; Work `17*clearMaximum+529`, clock `clearMaximum+46`, and a postcondition supplying the final logical-length bound.
- `ExtendMemoryAllocRestore.lean`: actual continuation116 restores capacity/next-capacity and moves the expansion word to its next saved slot; memory outside its four writes is preserved.
- `ExtendMemoryAllocTransfer.lean`: actual allocator call134 plus callee/continuation; saved values survive under explicit pointer-cell and handler-metadata separation. Memory outside the combined six possible write locations is preserved.

**Crucial limitation of memzero's memory theorem:** every existing word remains a word with unsigned value no larger than before. This supports upper bounds even with overlap. It does **not** prove exact saved values or correct guest memory contents after arbitrary overlap. Do not use it as a general separation/correctness theorem.

## 6. Suggested implementation order after a positive feasibility decision

1. **Freeze the chosen interfaces and budget table.** Keep unknown obligations named. Choose the next proof by its effect on the critical path.
2. **Prove global initialization and a small invariant-preserving cycle.** Include a real call/return and a failure path. Check that the invariant can express bitvector ranges, domains, code/oracle installation, and frame ownership without circular assumptions.
3. **Prove the dominant total resource bound.** Depending on the feasibility review, this may be gas-pool accounting, adversarial table work, input reduction, or nested cleanup. Do not automatically finish every library routine first.
4. **Complete only the required local summaries.** Reuse existing contracts; strengthen postconditions when composition needs them. Avoid new wrappers that merely repackage the same unresolved global hypothesis.
5. **Compose one full path through the exact compiler/target interfaces early.** A small covered path is a plumbing test, not the universal result. Do it before proliferating similar proofs.
6. **Expand to exhaustive coverage**, updating the work inventory and numeric total after each family. Separate success, rejection, timeout, exception, and excluded-source cases according to the actual semantics.
7. **Close the whole-entry work and clock theorems**, instantiate target composition, compute K with exact arithmetic, and package the certificate.
8. **Validate the actual final artifact** under the permitted resource/verification policy. Tighten K only after an accepted finite certificate exists.

If the chosen route still needs the current allocator connection, the concrete next local task is:

- Derive `ExtendMemoryCapacityEntry.Ready` from `ExtendMemoryAllocTransfer.saved_state` after actual call134. Preserve the metadata, frame, and memory-base lookup cells using the combined write footprint; transfer domains, installed memzero code, registers, and the bounded saved expansion.
- The callee writes the allocator pointer cell `globals-32` and its return-save cell `callSP-32+24`. The continuation writes `metadata-56`, `(callSP+24)+40`, `+32`, and `+24`. Prove required lookup cells are outside these locations; do not assume this merely because they represent different concepts.
- Then prove the earlier actual save/setup establishes allocator `Ready` and the needed separation. Call134 is surrounded by handler setup in block139; it is not entered directly from the function ABI.
- Connect the growth arithmetic and outer branch. Capacity clearing (`nextCapacity-capacity`) and logical expansion (`expand_by`) are different lengths and need different bounds. Prove the required no-wrap/range facts.

Useful navigation in fixed `submission/InitECandidate/Proofs/BackendStages/Named484.lean`: routine484; allocator call134 and continuation116; suffix248 after allocator return; capacity memzero call214 and continuation202; capacity suffix237; final memzero call325; final suffix363; capacity conditional264; whole body380. The fixed files are read-only for this task.

## 7. Measurements: useful evidence, not a certificate

See [PHASE1-REPORT.md](work/agent-notes/PHASE1-REPORT.md) for full methodology and caveats.

| Quantity | Measured/documented result |
|---|---|
| All EEST records | 33,614; min48,245; max12,288,467,579; mean8,980,605.947 Spike instructions |
| Declared gas ≤200M subset | 32,444 records; max4,654,270,509; mean8,478,606.534 |
| Largest covered observed instructions/payload-gasUsed ratio | 5,168.308, BN254 pairing fixture28355; payload gasUsed is not independently measured consumption |
| 128MiB-arena-sized malformed zero input | 151,043,185 Spike instructions at declared gas0 |
| Collision microbenchmark | 4,096 deliberately colliding keys: incremental895,378,232 instructions; growth approaches53.4·N²; whole-block reachability is unproved |
| Current guest ELF SHA-256 | `af59ed6b844728699f84d400c4195e3765e1829465ae1fb6b6149fa869a1215e` |
| Reconstructed ROM | 950,344 bytes; SHA-256 `22a1dd0963f12a3492e647b2626101fad2312dfcff813978b8ff1aca9897d7cc` |

The current ELF/ROM do not match stale `BASELINE.json` provenance. The reconstructed current ROM matched the current ELF binary by file comparison; this was not a full Lean ROM-equality proof. The first208 bootstrap bytes have a separate checked encoding equality.

The old design envelope was `10^7*G + 10^7*B + 10^12`, giving3,343,177,120,000,000 at G=200M and B=134,217,712. **Its shape and coefficients are guesses for planning. Never insert it into `claim.json` without proof.** Quadratic or multivariate accounting may be needed before reducing bounded dimensions to a final constant.

Both formal evaluators are noncomputable in the relevant definitions. No executable mirror/agreement theorem or measured formal-clock corpus was built. Do not promise `#eval` as a shortcut. Full per-fixture joined data is at `work/baseline-steps/steps-and-gas.json`; compact summaries and synthetic measurements are in `work/agent-notes/`. Large raw data/logs may be ignored by Git and may not exist on another machine.

## 8. Working constraints and resource-safe commands

Existing user constraints persist unless changed explicitly:

- Work locally/offline. Do not contact outside the server, push, open a PR, run Yukon submission, or merge anything. Dependencies were installed earlier with permission; do not reinstall or update them by default.
- Do not run the full baseline audit, full verifier, unqualified `lake build`, or a build of the full `Solution` merely to test a helper. The baseline closure can consume approximately120GiB and was designed for112GiB RAM.
- Use the case-sensitive filesystem. `Tools/` and `tools/`, `Guest/` and `guest/` are distinct.
- Machine at checkpoint:16 CPUs, roughly30GiB RAM and31GiB swap; disk57% used, about126GiB free. Recheck actual values. Stop heavy work if disk exceeds85%; keep observed host-used memory below24GiB.
- Only `submission/Solution.lean`, `submission/claim.json`, and `submission/InitECandidate/Solver/` survive Yukon replacement. Fixed Proofs/ROM, trusted contract, and dependencies must not be modified to make a proof pass. This file and notes are local handoff artifacts, not submission payload.
- Use only `propext`, `Classical.choice`, and `Quot.sound`. No `native_decide`, native proof axioms, extra axioms, or unfinished proof holes in the final result. If temporary holes are introduced, list each by file/declaration and remove them before claiming a checked result.

Pinned Lean: `leanprover/lean4:v4.33.1`. Pinned Flapjack: `034bb5a1ed0b757082768d5406206bd2f8e31b7c`. Verify [lake-manifest.json](lake-manifest.json); do not replace pins with current upstream versions.

Start with cheap observations:

```bash
cd /root/evm.fast-dev
git status --short
git branch --show-current
free -h
df -h .
nproc
```

For one selected module, use a unique log stem and the resource guard. This example is for a future authorized proof session, not an instruction to rebuild now:

```bash
task_log=work/agent-notes/logs/your-unique-check
LAKE_ARTIFACT_CACHE=false python3 tools/baseline-resource-run.py \
  --max-used-memory-gib 24 "${task_log}-resources.jsonl" -- \
  /usr/bin/time -v -o "${task_log}.time" \
  python3 tools/limited-lake.py --work-dir "$PWD/.lake/lean-limit" --slots 2 -- \
  lake build InitECandidate.Solver.GuestWork.ExtendMemoryAllocTransfer \
  > "${task_log}.log" 2>&1
```

The prior session raised concurrency to a **shared four-slot pool** after measuring headroom. Prefer one limiter invocation with several targets. Independent limiter invocations can create separate pools; never accidentally run four workers per job. If deliberately using concurrent invocations, share the same valid `LEAN_LIMIT_REAL`, `LEAN_LIMIT_LOCK_DIR`, and `LEAN_LIMIT_SLOTS` environment as the parent launcher. Do not copy an old ephemeral lock-directory name blindly to a new machine.

If a tool observation times out, poll the same session or inspect actual processes. Do not restart based on elapsed observation time, an old log, or a lock file. A session/process confirmed live is a wait; a terminated build with errors needs a fix. Preserve raw logs, and do not overwrite a successful log after indexing it.

Use `rg` to locate files. Generated proof/ROM lines can be enormous: limit both lines and columns when reading, e.g. `sed -n '1,80p' FILE | cut -c1-240`. Do not dump whole generated modules or the entire proof manifest into context.

## 9. Evidence, commits, and final verification

After a successful targeted build:

1. Require a successful exit, `Build completed successfully`, and no `error:` lines. Check each main theorem's `#print axioms`.
2. Index only complete successful logs whose source has not changed:

   ```bash
   python3 work/agent-notes/record-proof-build.py GuestWork YOUR-SUCCESS.log
   # Use FlattenWeighted, etc. for other Solver subdirectories.
   ```

3. Update [PROGRESS.md](work/agent-notes/PROGRESS.md) with command/log, elapsed time, resources, result, failed attempts, assumptions, and remaining obligations. Update this file's top checklist.
4. Run the incremental policy check when appropriate:

   ```bash
   python3 work/agent-notes/check-solver-policy.py
   ```

   It checks Solver imports/tokens and package sizes, relying on prior checks for fixed files. It is **not** a trusted axiom audit, comparator run, or isolated verification. It writes `policy-check.json`; commit refreshed evidence with its corresponding source.
5. Commit small coherent checkpoints to the local working branch. Force-add only selected ignored notes/scripts/JSON evidence, not raw logs or generated fixture corpora. Never force-add all of `work/`.

Final checkpoint evidence: [proof-checks.json](work/agent-notes/proof-checks.json), successful `work/agent-notes/logs/extend-memory-alloc-transfer-v2.log`, and the source commit `04603be4d`. That log covers the final allocator dependency closure. Other prior successful logs are named per fact in the manifest. A failed Lean build can print `sorryAx` through error recovery even without an explicit source hole; never use such a log as successful proof evidence.

Useful generator scripts for the latest work:

- `work/agent-notes/generate-frame-alloc-all-clocks.py`
- `work/agent-notes/generate-frame-alloc-state.py`
- `work/agent-notes/generate-memzero-memory.py`

Generators are untrusted scaffolding; Lean checks their output. Before rerunning one, inspect which files it overwrites and preserve intentional edits. Static Crep/Word/Stack batches are finished; do not restart their old drivers.

Transport limits are distinct: Yukon overlays have25MiB compressed /512MiB expanded /10,000-entry limits; the verifier's complete package has65,536 entries,16MiB per file, and4GiB total. The large fixed proof library is reused under the challenge's overlay rules. Do not compare the whole fixed checkout directly to the overlay cap or assume passing one limit proves the other. Check the actual final overlay and full package separately.

Official acceptance requires the unchanged comparator verifier and kernel replay, on a host meeting isolation requirements. Build-only mode is not official acceptance. Under the current user's constraints, do **not** run either full verification mode on this machine. When the finite theorem is ready, report the exact artifact and the verification still needed; obtain an authorized suitable verification environment rather than claiming local helper builds establish the final certificate.

## 10. Lean and proof-engineering traps already encountered

- Qualify `StackSemStateOps.getVar` and `getVarImm`; similarly named Loop helpers can elaborate incorrectly.
- `StackSem.locCheckExact` is a proposition. Do not accidentally compare it to Boolean `true`.
- A bitvector `==` returns Bool. When a match is stuck, expose `(x == y) = false` using `beq_eq_false_iff_ne`, rather than assuming a `x ≠ y` hypothesis rewrites every context.
- Simplification may normalize `address + 0` in the goal but leave a domain hypothesis in another form. Normalize hypotheses consistently. Use checked bitvector lemmas such as `BitVec.sub_add_cancel`, not natural-number arithmetic on wrapping addresses.
- `prefix` and `protected` are reserved identifiers in relevant syntax; use `blocks` or `protectedReg`.
- `BlockBound.basic` can shadow the `FlattenWeighted.basic` predicate inside a theorem namespace. Qualify the predicate when needed.
- `nodes` counts syntax constructors, including sequences; it is not merely the number of instruction leaves. Composing smaller basic blocks may avoid paying sequence-node overhead repeatedly, but preserve the actual program structure.
- A normal postcondition is vacuous after return/halt/error/timeout. Use this fact to avoid assuming successful loads, but do not accidentally omit exception/unwind paths that really continue.
- `Work.mono` may need an explicit `first := ...` before `omega`; otherwise the intended lower credit is an unconstrained metavariable.
- Huge record/installed-code equalities can make `assumption` unfold enormous terms. Reconstruct invariant records with explicit field projections rather than searching all hypotheses.
- After `simp at run` closes impossible branches, subsequent tactics may have no goals. Use appropriate `all_goals` blocks. Splitting a nested match may move the useful equation into a new hypothesis; splitting only the original `run` may miss it.
- Generated deep indentation matters: a poorly indented closing `simp ... at` line can cause the next tactic to parse as another location. Keep multiline generated tactic arguments aligned with the surrounding proof.
- Module hashes and axiom manifests must match current source, not an earlier successful version. A warning is different from a proof error, but inspect both.

The best next result is not necessarily another checked lemma. It is evidence that the full proof can be completed with a bound under the score cap—or early, specific evidence that the route must change.

- With Flapjack imports, a bare `word >>> 3` may infer a word-valued shift
  amount through `RiscV.bitVecWordShiftRight`. Use `word >>> (3 : Nat)` when
  matching `wordShiftHOL`'s natural shift count. QueryBranch's failed elaboration
  exposed this mismatch; its checked source now states the natural count.
