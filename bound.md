# Status — update this section frequently

**Objective corrected by the user on 2026-10-17:** obtain a reasonably tight finite runtime bound for the **CURRENT, UNCHANGED Pancake implementation on `main`**. There is **no required numerical ceiling**. In particular, exceeding Yukon's score limit is not a failure and does not authorize replacing an algorithm.

**Pinned reference:** local `main` is `7d656e5b6878aa420de793d9d6f689fa26ec0842`. `Guest/Ast.lean`, `Guest/guest.pp.pnk`, `submission/Solution.lean` and `submission/claim.json` currently have no changes relative to `main`. Do not change the program, its data structures, compiled ROM or semantics to improve the bound.

**The goal is NOT complete.** No whole-program finite bound has been proved. The submission still claims infinity. The earlier 45% estimate concerned the previous, misdirected plan and must not be reused as a progress estimate for this corrected task.

**Plan correction:** stop radix replacement, cross-program equivalence and candidate compilation work. Retain existing work until its dependencies have been reviewed, then remove unneeded code under the cleanup item below; Git retains its history. Reuse checked theorems that apply to the unchanged program: input parsing, hashing, allocation, original hash-table construction/lookup, gas accounting and quantitative compiler/boot results. Judge applicability from theorem statements; some original-program helpers live under `WitnessRadix/` and are still useful. Replacement-only results are historical reference, not remaining obligations.

**Original-table budget:** the previously proposed witness-construction allowance of 21,004,777,811,675,496 is a conditional partial upper bound, not a whole-program result or a lower bound. Its exceeding Yukon's score cap is irrelevant to the corrected objective. Resume accounting for the original tables, improving dominant slack where justified and retaining explicit conservative terms where needed.

**Current authorization:** continue autonomously toward the corrected goal. The user's earlier no-stop-point instruction remains in effect. Local/offline, memory/disk, permitted-axiom and full-verifier restrictions remain in force. Do not silently reintroduce a score threshold or an implementation change as a prerequisite.

**New checked actual frame_epilogue body/caller:** unchanged frame error160 and continuation snapshot24 loads select the real state_restore call. Both branches now retain all physical table models, journal image/whole reservation and exact counter. Success removes0 records; error removescount−min(count,snapshot), including later-snapshot no-op. Body pays<=Journal.price(D,count−snapshot)+1 on errors and0 on success; outer caller adds1, with whole-family potential accounting and derived funding/room. Successful frame-epilogue-call-v1.log1527jobs, exit0, permitted axioms, MaxRSS1955752KiB. Counter/cell ownership/code/population/global reachability remain explicit; low scratch-memory/gas-ledger preservation and the complete run_frames cycle remain open. Index4945modules/8381facts; claim infinity; no whole-program K/full verification.

**New checked complete original state_fresh_tx:** actual72-byte record allocation, all eight unchanged htab_new calls, actual pointer stores, block-state pointer and journal_n reset now compose through the complete body and ignored-result caller. Normal execution derives all reached room and clock funding. Body81source clocks/caller82; persistent cursor advances17176bytes. Every old table survives, eight actual empty tables have distinct identities and matching stored pointers, and the complete unused journal reservation survives with actual count0. Incoming family/zone/heap/code/bs/ts facts remain explicit. Successful state-fresh-tx-call-v2.log1603jobs, exit0, permitted axioms, MaxRSS1987168KiB; includes journal initialization and both append callers. Index4940modules/8373facts; baseline unchanged, replacement reverse closure0. Source clocks omit straight-line work; global reachability/event counts/frame exits/weighted target K remain open. Claim infinity; no full verification.

**New checked original storage-key warming loop:** the exact `process_transaction` loop over 52-byte input keys now has a complete normal-execution source-clock/model bound. Its signed counter derives the number of actual setters; alternating key alignments are mapped from the owned input interval. Every actual setter derives reached allocation room, returns the next valid physical table/half occupancy/power/heap cursor, preserves caller locals, and protects all words below the table lifetime floor. For initial population D and n remaining keys, paid+P(initialCapacity)<= (13D+17)*n+13*triangle(n)+P(finalCapacity); final population is in[D,D+n] and final capacity<=max(initialCapacity,4*(D+n+1)). A checked path through the real post-MSG_GAS suffix supplies an actual normal loop execution and retains the message binding. Successful root-warm-keys-complete-v1.log1363jobs, exit0, permitted axioms, MaxRSS2093836KiB. Entry input extent, initial constructor/table ownership and global reachability are still explicit; source clocks omit straight-line work, so this is not target runtime K or whole-program completion.

**New checked constructor reachability for storage warming:** actual successful original htab_new at word-multiple capacities now derives all six allocation guards and the final fresh layout, through the initial stride/header stores, three pre-clear allocations, actual memzero and two final allocations. Actual store outcomes establish their frames without supplied mappings; actual memzero derives its price and unchanged heap cursor by clock padding. The original storage constructor(52,16), counter reset and complete warming loop now compose from ordinary bounded/aligned incoming heap cursor, code and input-interval facts, with no prospective allocation room, pre-existing empty-table model or entry-clock allowance. Constructor contributes exactly10 source clocks; cumulative price is10+17*n+13*triangle(n)+P(finalCapacity)-P(16), understood as the checked additive inequality. All words below the incoming table cursor survive. Successful root-warm-constructor-normal-v1.log1384jobs, exit0, permitted axioms, MaxRSS1885544KiB. Actual input-region/cursor/code reachability, other warm-up loops and subsequent root/message execution remain open; this is not target runtime K or full verification.

**New checked original account-table/precompile prefix:** exact original account constructor(20,64), sender setter, both literal skips, counter reset and all18 precompile-address warm-ups now compose on the actual normal caller execution. The constructor derives its six-allocation room/empty model. Actual population<=1 after the sender call and <=19 after the loop rules out every growth; all globals/heap and words outside the same table pools survive these setters. Combined source-clock bound1795 (=10 constructor+12 sender+1773 loop), with no entry-clock allowance or prospective allocation room. Every word below the incoming account-table cursor is preserved, including protected earlier message cells. Successful root-warm-precompile-constructor-v3.log1386jobs, exit0, permitted axioms, MaxRSS1931560KiB. Original code/domain/heap entry bounds, actual mapped sender/precompile inputs remain explicit. Access-list address warming, subsequent storage warming composition, global reachability/gas and target K remain open.

**New checked complete original transaction table warm-up:** both actual warm-table constructors, sender,18precompiles, coinbase/access-list addresses and all storage keys now compose through their real caller scopes. The address queries are genuine loads from an exact protected pointer array, preserved through every reached setter/growth. Both final Header/Occupied models are live, half full, power-of-two, naturally separated and share the actual final heap cursor; the account model survives all later storage-table allocation/mutation. All words below the incoming account-table cursor and all caller locals except aa/ak/i are retained. The combined additive source-clock bound is paid+P_account(64)+P_storage(16)<=1805+(184A+9triangle(A))+(17S+13triangle(S))+P_account(Ca)+P_storage(Cs), with Ca<=max(64,4(A+20)), Cs<=max(16,4(S+1)). WarmTables.price eliminates final capacities to a concrete finite function of A,S. Actual source heap/code/domain, sender/precompile mappings, owned exact address-pointer array and key-buffer extent remain entry obligations. Successful root-warm-tables-price-v1.log1404jobs, exit0, permitted axioms. Input/message construction reachability, later destination setup/final setter/message call, global gas coupling and weighted target transport/K remain open. This is source-clock accounting, not a whole-program runtime certificate or full verification.

**New checked original persistent message constructor:** actual msg_new body and real scoped caller now derive the reached176-byte reservation, every cleared word, exact heap/returned pointer and normal continuation, with no future-room predicate or entry-clock allowance. Body cost9source clocks, caller10. All memory outside the exact allocation survives. Successful message-new-call-v2.log1161jobs, exit0, permitted axioms, MaxRSS1860576KiB. Incoming ordinary heap lower/upper/alignment, source domain and canonical allocator/trap/memzero/msg_new code remain entry facts. Actual caller message stores/MSG_GAS and its preservation through the complete warm-table stage are next; global gas/target K remain open.

**New checked actual message gas through warm-up:** original msg_new, four pre-gas field stores, actual MSG_GAS store, reservoir store, real four-word value load/store and every original table warm-up now compose through all real m/aa/ak caller scopes. Allocation establishes the176-byte message and its position before both warm tables. Actual scalar/tuple widths derive finite store footprints; earlier input words survive, as does the physical MSG_GAS word and message binding through every allocation/growth. The combined phase costs at most10+WarmTables.price(A,S) source clocks, with no entry-clock or prospective-room allowance. A two-local actual-path theorem carries mgas and reservoir to the same allocation state; the unchanged validator/root split derive these words and gas+intrinsicRegular<=16777216 without gas/helper/clock oracles. Heap/input models and be/te/sender/array/key bindings at that reached state remain caller-reachability obligations; later recipient/create setup, final account warming, process_message_call/active frame, global accounting and weighted target K remain open. Successful combined root-message-validated-v1.log1421jobs, exit0, permitted axioms, MaxRSS2099260KiB; includes initialized_normal and validated_entry. The proof's first field was corrected to the original global be read; fixed guest/ROM/Solution/claim remain unchanged. These are checked conditional source-clock/dataflow contracts, not a whole-program runtime certificate or full verification.

**New checked full non-creation message setup:** the actual original path from msg_new through all message stores, both full warm tables, the reached8byte empty allocation, real recipient test/six stores, final account setter and both table-pointer stores now reaches the exact process_message_call declaration through its real m/aa/ak/empty scopes. Actual final insertion may grow account arrays past the storage table; per-pool separation preserves both complete physical models and the root MSG_GAS word. Generic executed scalar stores preserve unrelated table pools, copied transaction fields are protected by the earlier400byte transaction record, and untouched caller bindings/capacity high-water facts survive the earlier phase. With A account queries and S storage keys, noncreatePrice is1999+WarmPrecompiles.price(19,A)+9A+WarmKeys.price(0,S)+P_account(max(64,4(A+21)))+P_storage(max(16,4(S+1)))-P_account(64)-P_storage(16), using natural subtraction as checked. Growth charges telescope across the whole phase. Successful root-recipient-noncreate-v1.log1433jobs, exit0, permitted axioms, MaxRSS1970680KiB. Entry input/transaction/query/code/heap models remain explicit. Creation transactions, preprocessing reachability, subsequent message/frame execution, global gas/event counts and weighted target K remain open. No whole-program finite bound or full verification is claimed.

**New checked message-call/frame entry bridge:** actual process_message_call allocates and clears its96byte output with derived room and exactly5source clocks, preserving every earlier object and both live table models. The complete original frame_open body/caller now derives available clocks from actual normal execution via exact temporary padding; no entry-clock allowance remains. Its returned/activated child has regularBudget equal to the physical MSG_GAS word. The actual process_message depth guard and parent scopes reach this call and retain its real continuation/scopes. For the root's empty-code message, owned176byte message geometry and actual warm-table headers derive all constructor message/table-count mappings and protected reads; zero code length eliminates the code-buffer mapping premise. Original arena/code/global/room reachability remains explicit. Root setup additionally exports the exact stored reservoir, empty-code pointer and zero code length through all warming and final insertion. Successful root-frame-input-fields-v1.log1504jobs, exit0, permitted axioms, MaxRSS2723952KiB. Creation, dispatch/remaining message execution, arena/input/decoder reachability, global gas/event counts and weighted target K remain open; these conditional source-clock/dataflow results are not full verification or a whole-program finite bound.

**New checked actual root-call to active gas ledger:** actual normal scalar stores now derive mappings/exact memory effects from their executed reads. The original transaction recipient copy into MSG field24 survives initial stores, MSG_GAS, remaining stores, every warm-table mutation and recipient setup; its value is tied to the actual protected transaction record. Original process_message_call therefore takes its genuine non-creation dispatch and the actual assigned process_message body reaches the active child through its real depth guard/parent scopes/frame_open. Output allocation/clear preserves all old constructor inputs by owned interval/header bounds. The body prefix pays at most length+memzero_price(bitmapBytes(length))+51 source clocks; its real root scoped caller adds1. The physical MSG_GAS word supplies both the initialized regularBudget and regularBudget+intrinsicRegular<=16777216, without a supplied ledger result/helper trace. The exact prefix can be53source clocks at empty code length under this allowance. Successful message-call-normal-open-v1.log1511jobs, exit0, permitted axioms, MaxRSS1935504KiB. Arena/code/cursor/input ownership and room remain explicit; creation, subsequent depth0 preparation/frame loop/global accounting and weighted target K remain open. No whole-program finite bound/full verification.

**New checked combined root setup to active frame:** complete non-creation setup now composes from the actual original msg_new declaration through both warm tables and real message dispatch to the active child. Every persistent setter/growth and warm loop preserves all non-heap globals; those frames telescope through constructors, initial stores and recipient setup, retaining the actual arena/parent/continuation/empty bindings. Owned message/table geometry derives the intervening read bounds; the original96byte output clear advances the reached heap. Both live physical warm-table models survive all output/frame/stack/bitmap/log/continuation allocations and share that advanced cursor. The initial active regularBudget equals the actual capped MSG_GAS, and the combined source-clock price is noncreatePrice(A,S)+53, with no clock/helper/intermediate-model premise. Source NoncreateSetup, canonical FrameCode and incoming ArenaEntry explicitly list remaining input/caller/code/arena/room reachability obligations. Successful root-active-frame-v1.log1515jobs, exit0, permitted axioms, MaxRSS1966668KiB. This reaches the genuine post-open process_message continuation; depth0 preparation, frame loop, creation, global phase counts and weighted target K remain open. No whole-program finite bound/full verification.

**New checked actual normal gas transitions:** original charge_gas now derives frame gas/used mappings and words, affordability and its single caller clock from actual normal execution; the capped physical ledger derives non-wrap and exact natural debit/counter credit. Every positive actual charge advances the irreversible regular counter. Original charge_state_gas now covers both full add_sat branches, including saturated combined-pool overflow; actual normal guards derive affordability without a sum-fitting, clock or exception-shape premise. Its real caller derives1or2clocks and preserves the capped regular ledger. Actual refund/refill callers derive exactly2/1clocks and preserve that ledger, with owned current frame/message reads still explicit. The existing SaturatingAdd execute/call/ge_left/fee API is retained; only carry/min/coverage arithmetic was added, and its existing ValueFee consumer was checked. Successful gas-normal-transitions-v2.log1592jobs, exit0, permitted axioms, MaxRSS1855800KiB. Actual opcode/event counts, ownership through all other mutations, exception/child paths, block accounting and target transport/K remain open. These are executed local contracts, not a whole-program finite bound or full verification.

**New checked actual frame-exception control:** original frame_halt now derives its caller clock/non-wrap from actual normal execution and the capped ledger, exports exact writes, clears liquid gas and retains the error marker. Both real frame_exception branches compose actual refill, optional halt, return-data/direct-error stores and final continuation-done store. Its normal body costs1or2source clocks and real caller2or3, all funding derived; regularBudget is preserved and the actual continuation word+32 becomes1. Nonmemory caller fields are retained. Current frame/message mappings/words and continuation separation remain explicit ownership obligations, not helper executions. Successful frame-exception-normal-call-v1.log1598jobs, exit0, permitted axioms, MaxRSS1827404KiB. Connecting this done marker to run_frames exits, all-opcode/child/rollback progress, global event counts, creation, caller/input/arena reachability and target K remains open; no whole-program finite bound/full verification.

**New checked live table family and original rollback prerequisites:** an arbitrary family now retains every physical table model and stable header pointer across an actual setter or deleter. Reached setter growth room and deletion funding are derived from normal execution; no extra entry-clock premise is supplied. An older word outside the writer pools stays outside relocated arrays and retains its value, covering journal allocations between old pools. The exact state_restore AST, actual unsigned guard/decrement (including high-bit counters), and its three real record declarations are checked. Both actual mutation branches preserve the complete journal image and copied query mappings. LocalPrefix additionally permits global assignments without changing its caller-local guarantee. Successful journal-records-mutations-v3.log1439jobs, exit0, permitted axioms, MaxRSS1910612KiB. The actual branch/loop composition, journal initialization/append/snapshot reachability, global rollback/event counts and weighted target K remain open. These are conditional original-program contracts, not a whole-program finite bound/full verification.

**New checked complete original journal rollback:** actual state_restore now composes its executed decrement, all three record declarations, actual flag branch, original setter/deleter, complete while loop, zero return and real ignored-result caller. For n=count-snap and entry population bound D, caller paid+P(familyEntry)<=1+(38D+40)*n+38*triangle(n)+P(familyExit). The unsigned counter derives the iteration count; every remaining journal image/table model survives, final counter=min(count,snap), and an already-restored later snapshot is checked as a no-op. Current journal image/family/extent and canonical code remain explicit entry reachability obligations; no helper trace, chosen mutation sequence or source-clock allowance is assumed. Actual state_snapshot also derives its one caller clock and saves exactly the current journal counter through its real scope. Successful journal-snapshot-restore-v2.log1522jobs, exit0, permitted axioms, MaxRSS1977732KiB. Journal initialization/append reachability and global rollback totals, all other phase/gas/ownership obligations and weighted target K remain open. This is a complete conditional source-clock rollback contract, not a whole-program finite bound/full verification.

**New checked journal append entry and copied-key ownership:** actual original htab_get now derives its result pair, binary flag, collision-sensitive clock price and complete nonlocal read-only frame from the physical table on a normal caller return. The real jset guard derives count<cap; jdel either takes its actual absent-key zero return or derives count<cap before appending. Actual trap4/5 are proved unable to continue normally, without treating their FFI effects as pure. The exact shared append prefix reads the physical key length, derives the reached allocation room/rounded cursor, executes the real memcpy with derived funding, and reaches the original record stores through its real scopes. It costs at most keySize+2source clocks, preserves every old table/live journal record and all old words below the allocation cursor, and establishes a fresh mapped key region. Zone records ownership of unused as well as live journal slots. Successful journal-key-model-v2.log1538jobs, exit0, permitted axioms, MaxRSS1978972KiB. Four record stores, increment/final mutation and complete jset/jdel caller composition, journal initialization/global accounting and weighted target K remain open. No whole-program finite K/full verification.

**New checked complete original jset:** actual original record declaration/four stores establish the new image without corrupting older records or any table pool. The real unsigned increment cannot wrap after the cap guard. The complete jset body/caller now composes its actual getter, guard, copied-key prefix, record stores, counter increment and final original setter. All live table models, unused journal slots, copied query mappings and noncontrol globals survive reached growth; final journal_n=count+1 and the saved flag/value are actual getter results. Caller paid+P(oldWriter)<=Get.bodyPrice(kind,D)+1+(keySize(kind)+2)+Set.noGrowthPrice(kind,D)+2+P(newWriter). Physical source family/image/reservation, current bindings/query mappings and canonical code remain explicit reachability inputs; no helper execution, intermediate model, future room or entry-clock allowance is assumed. Successful journal-jset-call-v1.log1550jobs, exit0, permitted axioms, MaxRSS1962932KiB. Complete jdel, journal initialization/global append/rollback totals, other phase/ownership/gas obligations and weighted target K remain open. No whole-program finite K/full verification.

**New checked complete original jdel:** actual original jdel body/caller now covers both real getter outcomes. An absent key returns with only its paid clock changed and costs at most Get.bodyPrice(kind,D)+2caller clocks. A present key takes the real cap guard, copies its key, appends the literal saved flag1/actual old value, increments journal_n, executes the original deletion and returns0; caller price is Get.bodyPrice(kind,D)+1+(keySize(kind)+2)+(Delete.modelPrice(kind,D)+1)+1. Physical layouts/capacities remain fixed, populations do not increase, and the entire family/live image/unused reservation and noncontrol globals survive. The actual present-path persistent cursor advances exactly by stride(kind), and final journal_n=count+1. Source physical/code/query/global reachability remains explicit; helper traces/funding/future room are derived. Successful journal-jdel-call-v1.log1556jobs, exit0, permitted axioms, MaxRSS1971144KiB, including the existing jset caller. Next strengthen rollback to retain the unused reservation after restoring, then prove journal initialization/global counts and frame-exit connections. Whole-program finite K/full verification remain open.

**New checked append/restore reservation interface:** the entire existing rollback branch/record/body/loop/return/caller chain now retains Zone for every unused journal slot as well as the live image and table family. Its former extent premise is derived from the current owned reservation/count<=cap. Both actual mutations use the complete reservation frame, including growth past old pools; the no-op snapshot branch retains it too. The same amortized rollback price remains. Successful journal-restore-reservation-v1.log1554jobs, exit0, permitted axioms, MaxRSS2009564KiB; both append callers and snapshot rechecked against the strengthened chain. This closes the conditional ownership interface for subsequent appends after rollback, not whole-program reachability. Journal initialization, table-family extension at actual constructors, global counts/other state mutations and weighted target K remain open.

**New checked original journal initialization suffix:** the exact journal_cap/alloc/journal_n/ts suffix selected from unchanged state_init now derives its16MiB reservation, single allocation clock, all real global updates and zero return from normal execution. Actual assigned-global allocation derives room and full caller state. Actual scalar assignments derive valid updates without old-value or shape premises. The result establishes capacity524288, journal base, advanced bounded/aligned cursor, zero live counter/ts, empty image, the full unused reservation and every preceding table model. Source current heap geometry/journal binding/allocator code and pre-existing family remain explicit entry reachability obligations; earlier witness/state/table construction is not priced by this suffix. Checked identity extension preserves old table models and lifts journal entries/reservation when a fresh table is added after their cursor; linking this to actual constructors is next. Successful journal-init-owned-v2.log1563jobs, exit0, permitted axioms, MaxRSS1951288KiB; includes both append callers and strengthened rollback after LocalPrefix gained checked global-result call support. No whole-program finite K/full verification.

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

**New checked full small-key comparison fallback:** both actual byte loops, every mismatch/advance, final return/scopes, mapped reads and caller ABI now check for all lengths<=64. Caller allowance is length/8+length%8+1 source clocks (20=>7,52=>11,60=>12), with return0or1 and pure canonical state. Uniform20/52-byte comparison and hash callers now derive every read from mapped byte regions, covering either alignment; no comparison/helper result is assumed. Comparison permits adversarial arbitrary contents. Successful combined key-helpers-mapped-v1.log1216jobs, exit0, permitted axioms, includes retained root/frame/record closures. These are intermediate source-clock contracts, not generic mutable-map progress/ownership or a target runtime K.

**New checked original account/storage lookups:** complete unchanged htab_find_slot, htab_get and htab_has bodies and real scoped callers now derive actual headers, hash, masked index, arbitrary-collision probe scans, comparisons and absent/present value reads for20/52-byte keys at either alignment. With D covering occupied slots and D<capacity, actual find callers consume at most8*D+2/12*D+2 source clocks; get/has callers at most8*D+3/12*D+3. Physical header/typed values, byte-region ownership/no-wrap, binary used slots/coverage, capacity, code and entry clocks remain explicit. The finite scan is derived from occupancy and masked-index injectivity, not assumed. Successful get-sized-call-v1.log1129jobs and has-sized-call-v1.log1132jobs, exit0, permitted axioms. These contracts give runtime and pure frames, not full logical dictionary semantics; mutation/growth/deletion and global count/ownership reachability remain open. No whole runtime K or target bound is claimed.

**New checked indexed-key fallbacks:** the actual generic htab_hash body/caller now derives all byte loads, folds, both loops and avalanche return for small key widths other than20/32/52, including28/60. Its exact caller allowance is length/8+length%8+1 source clocks (8/12 for28/60), with either alignment and pure canonical frame. The actual aligned memeq fallback now covers the extra32-byte loop,8-byte loop, both later byte loops, every early mismatch and final return/scopes; combined with the byte fallback, mapped inputs derive a uniform comparison caller for these widths with the same8/12 allowance. Successful combined memeq-other-mapped-v1.log1119jobs, exit0, permitted axioms. No lookup/mutation/global/runtime/target conclusion for28/60 is claimed yet; physical no-wrap/code/mapping/entry-clock premises remain explicit.

**New checked original indexed-key queries:** complete unchanged htab_find_slot/get/has bodies and scoped callers now check for28/60-byte keys at either alignment, including real generic hashing, finite arbitrary-collision probe chains and actual value/absent returns. Find caller allowances9*D+9/13*D+13 and get/has9*D+10/13*D+14 source clocks, for D covering occupied slots with D<capacity. Normal code/physical header/typed-value/no-wrap/mapped-region/used-byte/order/clock premises remain explicit. Successful indexed-query-call-v2.log1255jobs, exit0, permitted axioms, includes retained frame/root closures. These are runtime/pure-frame contracts, not logical map correctness or mutation/reachability/global/target K. Original key widths20/28/32/52/60 are now covered by checked lookup paths under their respective entry hypotheses.

**New checked whole original raw insertion:** complete unchanged htab_insert_raw body and ignored-result caller now derive all seven header reads, actual hash at each original key width, finite first-empty scan, arbitrary-alignment memcpy, value/used/order/order-position/count stores, return/scopes and exact final memory. Generic byte-region ownership derives all copy mappings; no successful helper run is a premise. Caller allowance is D+hash_price(width)+width/8+width%8+2 source clocks: D+9/17/7/13/25 for20/28/32/52/60bytes. The final physical count cell is exactly count+1 (64-bit word); natural no-wrap and full map invariants still need reachability. Physical data is independent of caller parameter names and actual ABI derives locals. Successful insert-general-call-v1.log1146jobs, exit0, permitted axioms. All per-slot ownership/header separation, code/room/used coverage and clock entry premises remain explicit. This is NOT an actual growth/deletion invariant, global phase bound, logical map specification or target runtime K.

**Query proof consolidation checked:** one common physical probe/lookup/get/has contract now covers every original key width20/28/32/52/60, preserving the prior bounds and pure frames. The32-byte runtime contract additionally exports the returned slot/capacity bound needed by setters. Removed20 superseded width-specific query modules and160 stale build artifacts (14,780,408bytes), retaining all shared original hash/comparator and logical32-byte witness helpers. [Cleanup manifest](work/agent-notes/query-runtime-cleanup.json) records source hashes and the zero-external-importer audit. Successful retained combined general-query-cleanup-v1.log1267jobs, exit0, permitted axioms; includes original raw insertion and retained root/frame closures. This consolidation supplies local contracts only; actual mutable-map ownership/count invariants, growth/deletion and whole-program/target bounds remain open.

**New checked whole original setter without growth:** under the actual occupancy condition count<=D and2*D+2<=capacity, the real growth test is derived false. The entire unchanged htab_set body/caller derives actual lookup, existing-value update or absent-key raw insertion, scopes and exact nonlocal/memory/clock frame. Physical count remains count or becomes count+1; this occupancy condition excludes count-word wrap. Caller source-clock allowances are9D+12/10D+27/7D+10/13D+16/14D+39 for20/28/32/52/60-byte keys. Successful set-no-growth-budget-v1.log1161jobs, exit0, permitted axioms. Actual table ownership/used/order/count reachability and capacity assumptions remain explicit. Growth/deletion/rollback and global/target runtime are NOT closed by this result.

**New checked generic table ownership:** natural owned pools now derive every actual slot's mapped key/value/used/order/position cells, no-wrap key footprint and protected header cells for all original widths. Fresh six-allocation and relocated five-array layouts both prove separation/alignment, including used-array padding and a prior header either below or above relocated arrays. The stride equals the unchanged constructor's exact word expression. A physical nine-word header and binary occupied-slot/dense-order/position representation now derive the entire table-side GeneralData entry predicate for checked query/insertion/setter contracts, leaving input-query mapping/code/endian, capacity/order room and actual reachability explicit. Successful table-memory-entry-v1.log1272jobs, exit0, permitted axioms, includes retained root/frame/setter closures. Actual generic constructor establishment and mutation preservation of this representation, growth/deletion/global accounting and target K remain open; geometric predicates are not claims of reachable table states.

**New checked whole original persistent table constructor:** unchanged htab_new body and actual scoped caller now check for every original key width20/28/32/52/60. All six allocators, stride computation, nine header stores, both used-clear branches, return/scopes, exact heap/memory/clock and every outside-reservation memory frame are derived. The caller price is12 source clocks at capacity4, otherwise memzero_price(capacity)+8 for supported word-multiple capacities. Exact reservation is72+(stride+24)*capacity+round8(capacity); at capacity%8=0 this is72+(stride+25)*capacity. Actual completed clear/header writes establish the empty occupied/dense-order/position model and supply table-side runtime entry data for queries/insertion/setters. Original code, input query, heap cursor/room/alignment/domain, capacity shape/power and clock reachability remain explicit. Raw insertion additionally exports that its selected slot was empty, a complete untouched-word frame, and preservation of all nine physical header meanings with count+1. Successful combined table-runtime-budget-v1.log1309jobs, exit0, permitted axioms, includes retained root/frame/setter closures. This is NOT mutation preservation of occupied/order arrays, actual growth/deletion/global accounting or target runtime K.

**New checked lookup selection and setter effects:** the actual common lookup body/caller additionally proves that its result is the absent-cap sentinel or an in-range physically occupied slot. Binary used/order coverage derives an actual used byte1 and membership of every present result; an empty table forces absence. The unchanged no-growth setter body/caller additionally exports its exact effect: update an occupied value cell, or perform complete raw insertion into a previously empty slot. Prior clock allowances and count/no-wrap facts are retained. Successful find-general-selection-v1.log1170jobs and set-no-growth-effect-v1.log1163jobs, exit0, permitted axioms. These facts support mutation induction but do not themselves establish full occupied/order preservation, growth/deletion/global accounting or target K.

**New checked mutation representation:** actual existing-value stores preserve all nine header meanings and the binary occupied/dense-order/inverse-position invariant. Complete raw insertion sets exactly the selected byte (including neighboring bytes in its word), appends its previously empty slot, writes its inverse position and increments the count. Both actual raw-insertion and no-growth setter callers now establish their post-call physical model, for all five key widths and arbitrary collisions/alignment. Successful table-mutation-model-v1.log1220jobs, exit0, permitted axioms. The setter retains its earlier clock allowance; the raw caller costs at most D+hashPrice+copyPrice+2 source clocks. Entry ownership/query/code/clock facts remain explicit. Growth, deletion, global reachability/accounting and target runtime K remain open.

**New checked whole original growth:** all five key widths now have an actual htab_grow body and ignored-result caller contract: six old-header reads and doubling, all five allocations and rounding, actual memzero, seven reset stores, signed rehash loop, actual raw-insertion calls, return and every declaration scope. The post-call header/occupied/order/inverse-position model and unchanged old arrays are derived. The model itself derives D<=C; actual physical extents and the old power derive signed range, doubled probe power and clear shape. Caller allowance is `Zero.price(2*C) + triangle(D) + c*D + 7`, where c is10/18/8/14/26 for20/28/32/52/60-byte keys. Exact growth reservation is `(stride+25)*(2*C)`; the old header is reused. Actual growing-setter suffix also derives its guard, executes this growth and a final insertion, establishing count D+1 and the new model. Successful combined table-grow-complete-v1.log1294jobs, exit0, permitted axioms. Ownership/heap room, query/code/domain/little-endian/power/minimum/clock facts still require global caller reachability. This is NOT a whole general-setter/deletion/global-accounting or target K result.

**New checked complete original setter:** actual htab_set body/caller now composes lookup, existing-value update, absent insertion, actual count guard, optional growth, final insertion, returns and declaration scopes for all original widths. Its physical postcondition preserves the nine-word header, binary occupied/dense order/inverse positions, count in[D,D+1], and half-capacity occupancy. It derives current/doubled capacity, original power/minimum, actual heap word and all table pools below the returned cursor. Layout retention has the smaller linear no-growth allowance, even when entry occupancy could trigger growth for an absent key; actual growth alone adds its separate rehash allowance. Worst caller prices are `Zero.price(2*C)+triangle(D)` plus19D+19 /28D+34 /15D+17 /27D+23 /40D+46 for20/28/32/52/60-byte keys. Actual growth additionally requires C<2D+2 and implies new capacity<4*(nextCount+1), supporting population-based global bounds. Successful table-set-model-heap-v1.log1300jobs, exit0, permitted axioms. Potential allocation room/ownership, query/code/domain/clock reachability remain entry facts; deletion/truncation/copy APIs, global rollback/gas/counts and target K remain open.

**New checked original deletion components:** the unchanged htab_del AST is split with a checked shape; the physical occupied model initializes a moving-hole/dense-ordinal invariant. Actual movable-branch memcpy, value/position reads, three stores, hole assignment and scope restoration preserve it and all used/header bytes. The original unsigned decision and its home/movable scopes now compose both no-move and actual-move paths; a move costs at most copyPrice(keySize)+1 source clocks after hashing. A separate checked ordinal map proves the original final last-entry swap enumerates precisely the surviving ordinals, with distinctness, membership and length D-1. Successful table-delete-after-hash-v2.log1193jobs, exit0, permitted axioms. This is NOT the whole deletion/hash/scan/final-store/caller contract; those compositions, truncation and global integration remain open. The sentinel in the pending invariant exists only in proof data; no program memory or implementation was changed.

**New checked complete original deletion scan:** the actual htab_hash caller, unsigned movement decision, optional memcpy/stores and masked j increment now compose into the entire literal while loop, including its final empty-slot break. The physical occupied table initializes the moving-hole invariant and supplies a first empty slot within D occupied entries; masked-index injectivity proves each new occupied successor differs from the hole. Every iteration preserves used bytes, so the original snapshot bounds the whole scan. With D>0, the scan source-clock allowance is `(hashPrice(width)+copyPrice(width)+2)*(D-1)+1`, namely9/17/7/13/25 times(D-1), plus1, for20/28/32/52/60-byte keys. The physical header/pending order-position model and all other locals/nonlocal fields are preserved as specified. Successful table-delete-scan-model-v1.log1333jobs, exit0, permitted axioms, includes retained final-slot map and full setter closure. Final used clear/last-entry swap/count decrement, full deletion ABI, truncation/other APIs and global/target runtime remain open. This is an intermediate source-clock contract, not a whole deletion or finite K result.

**New checked original deletion final mutation:** the full scan now composes with the actual hole-byte clear, count read/decrement, optional last-entry read and two stores, count store, return and declaration scopes. The executed post-state has exactly D-1 entries with binary used bytes, dense order and inverse positions; the nine-word header retains its meanings with count D-1. The last-slot read/range are required only when its swap branch is taken. The final suffix uses0 extra source clocks, so the combined scan/final-mutation allowance remains `(hashPrice+copyPrice+2)*(D-1)+1`. This does not price its straight-line target instructions. Successful table-delete-scan-finish-v1.log1209jobs, exit0, permitted axioms. Full lookup/header/ordinal initialization and deletion caller ABI, remaining mutable APIs, global reachability/accounting and target runtime still remain open.

**New checked complete original deletion:** the entire unchanged htab_del body and actual ignored-result caller now compose the real find-slot call, cap read, absent return or seven header declarations, actual removed-ordinal read/J initialization, finite masked scan, all final stores, scopes and ABI. The physical post-model has unchanged layout and count D or D-1; absence preserves memory exactly, deletion success removes one ordinal, and half-capacity occupancy is preserved. Caller source-clock allowances for D>0 are17D-5 /26D-6 /13D-3 /25D-9 /38D-10 for20/28/32/52/60-byte keys. At D=0 the respective conservative caller allowances are4/11/4/4/15. Query ownership/no-wrap, table geometry/binary occupancy/order, code/domain/endian/power/clock reachability remain entry facts; no logical-key/self-lookup correctness assumption is used. Successful table-delete-complete-v1.log1349jobs, exit0, permitted axioms, includes retained full setter closure. This is an intermediate source-clock/model contract; truncation, copies/other APIs, whole global accounting and target K remain open.

**New checked original slot/item readers:** unchanged htab_slot derives every header/used-byte/value read and key pointer, then returns the actual tuple through all scopes; its scoped caller consumes exactly1 source clock. Unchanged htab_item derives its real dense-order read, tail-calls htab_slot and returns a used entry with the correct slot pointer/value; its scoped caller consumes exactly2 source clocks. All nonlocal fields remain unchanged. Physical owned pools/header/occupied representation, index/ordinal range, actual code/domain/clock reachability remain explicit. Successful table-item-call-v1.log1182jobs, exit0, permitted axioms. Source clocks omit straight-line reads; these are not whole global/target bounds.

**New checked complete original key enumeration:** unchanged htab_keys now composes both initial header reads, actual alloc, all output/header/counter setup, the signed loop, real dense-order reads and padded-stride memcpy calls, both increments, tuple return/scopes and actual caller ABI. Physical array extents derive the signed-safe count/index range. Exact reservation is `stride*D+8` bytes, already word aligned; the heap cursor and caller globals are derived. Caller source-clock prices are5D+2 /6D+2 /6D+2 /9D+2 /10D+2 for20/28/32/52/60-byte keys, including D=0. Full pool and outside-output word frames preserve the original table model. Successful table-keys-complete-v1.log1370jobs, exit0, permitted axioms; includes retained setter/deletion closures. Initial heap room/ownership/table/code/domain/clock facts still need global reachability. This prices source clocks, not straight-line target work, and is not a whole-program K.

**New checked complete original truncation on covered executions:** the actual htab_truncate body and successful ignored-result caller now derive last-position/slot reads, own-key arguments, real deletion calls, loop/scopes and return. No entry-clock allowance or logical NoGaps/self-lookup success is assumed. A no-change deletion would repeat the identical tail with less clock; exact finite-evaluator add-clock equality contradicts covered non-timeout termination. Every taken iteration therefore removes one entry, ending at m=min(D,n.toNat). A telescoping caller bound is `P(D)-P(m)+1`, where `P(D)` is17*triangle(D)+13D /26*triangle(D)+21D /13*triangle(D)+11D /25*triangle(D)+17D /38*triangle(D)+29D for20/28/32/52/60-byte keys. Exact layout, physical model/count and unchanged nonlocal fields are retained. Successful table-truncate-complete-v2.log1389jobs, exit0, permitted axioms, includes retained keys/setter/deletion closures. Original table/code/domain/endian/power and actual covered-run reachability remain explicit. These are source-clock/model results, not target runtime K.

**New checked original copy contents:** the actual unchanged memcpy word blocks and both aligned word loops now reproduce every copied full word from a separated owned source region. Byte projection proves the actual four-byte used-array copy, including preservation of neighboring bytes in the same word; supported capacity shapes therefore reproduce every logical used flag. These are exact memory-content lemmas for the real copy implementation, not an assumed copy oracle. Successful copy-used-contents-v1.log1132jobs, exit0, permitted axioms. The six allocations, header pointer rewrites, complete htab_copy body/caller, physical clone model and global reachability still need composition. No whole-program finite K or target runtime result is claimed.

**New checked complete original persistent clone:** unchanged htab_copy now composes both initial header reads, all six actual allocations and real memcpy calls, all five header-pointer stores, final scalar return/scopes and actual caller ABI. The clone has the same physical header/count, binary used flags, dense order and inverse positions. The original table model and every word outside the exact fresh six-pool reservation survive. Exact body source-clock price is `15+prefixCost(stride*C)+3*prefixCost(8*C)+(if C=4 then4 else prefixCost(C))`, where `prefixCost(n)=n/32+(n%32)/8`; caller adds1. At C=4 caller prices are26/27/27/30/31 for20/28/32/52/60-byte keys. Exact next heap cursor is freshEnd(kind,start,C), including used-array padding. Successful table-copy-call-v1.log1222jobs, exit0, permitted axioms. Actual old-table geometry/header/model, heap room, separation, domain/endian/capacity shape/code/clock reachability remain explicit. No target runtime or whole-program finite K is claimed.

**New checked mutation ownership frames and original call sites:** actual raw insertion/value update, no-growth setter, all growth setup/rehash iterations/body/caller, and the full general setter now export preservation of every word outside their written owned pools. General setter ModelPost carries this footprint in update/insert/grow paths; protected-word and disjoint-table theorems preserve arbitrary live message cells and complete unrelated Header/Occupied models. Successful table-set-ownership-v1.log1296jobs, exit0, permitted axioms. A separate kernel-checked traversal of every original function, including tail calls and exception handlers, proves no source declaration calls htab_copy_scratch and only compute_state_root calls htab_copy; original-table-call-sites-v5.log3017jobs, exit0, permitted axioms, MaxRSS7770688KiB. These are syntactic call-site facts and conditional executed mutation contracts, not global entry reachability, phase counts or whole-program finite K.

**New checked deletion/truncation ownership:** actual movable copies/stores and final clear/ordinal-swap/count stores preserve every word outside their table pools. This footprint now composes through every decision/hash/scan iteration, complete deletion body/caller and every covered truncation iteration, including clock padding removal and actual caller restoration. Both APIs preserve protected words and complete unrelated Header/Occupied models under disjoint ownership. Prior source-clock bounds and termination scope are unchanged. Successful table-truncate-ownership-v1.log1331jobs, exit0, permitted axioms, MaxRSS1887476KiB. Actual global object ownership and API-entry reachability remain open; this is not whole-program gas accounting or finite target K.

**New checked aggregate growth allowance:** actual general-setter postconditions and their existing two caller budgets now imply a telescoping price. With `P(kind,C)=triangle(C/2)/3+s(kind)*C`, s=7/11/6/9/15, the entire original growth caller allowance is paid by P(2C)-P(C) whenever count<=C/2 and original capacity is a power of two >=4. Each actual setter pays its ordinary no-growth allowance plus the increase of P; summing charges growth only across capacity increases, rather than once at worst-case size per mutation. Actual returned capacity is at most max(oldCapacity,4*(nextCount+1)). Successful table-set-amortized-v2.log1297jobs, exit0, permitted axioms. This is an actual-postcondition-linked conditional accounting lemma; caller event counts, table lifetimes, entry room and global gas coupling remain open, and no whole-program finite K is claimed.

**New checked original setter entry obligations on normal executions:** the fixed trap_with is proved unable to return normally for arbitrary FFI behavior. Actual normal persistent allocation derives request room, its clock and exact updated cursor/continuation; five actual growth allocations then derive the combined reservation and new layout validity. The setter suffix now asks for new-layout validity only when its actual lookup is absent and its natural growth threshold is crossed. A new full original setter body/caller bound derives that validity from actual normal execution and removes the entry-clock allowance with exact add-clock equality and padding removal. It retains prior price/count/capacity/header/occupied/ownership guarantees and returns the current layout validity, including updates where unused growth would not fit. Successful set-normal-call-v1.log1333jobs, exit0, permitted axioms, MaxRSS1863788KiB. Existing current-table/header/ownership/query/code/domain/endian/power/half-occupancy and aligned bounded heap-cursor invariants remain global entry obligations. No whole-program finite K or target runtime bound is claimed.

**Immediate next work:** integrate the now-checked original mutation APIs and ownership at actual global callers; aggregate their probe, growth, deletion and rollback costs. Connect actual message preprocessing to the capped root MSG word and active-frame/global regular-gas ledger, then child memory frames/merges, rollback and block counters. Derive startup/input/header, parser/failure, mutable count and trie/query progress premises from actual execution. Transport phase counts to the unchanged baseline target; no numerical ceiling applies.


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

The next results must connect checked original-program contracts to reachable states and whole-program counts. No score cap applies to the corrected task.

- With Flapjack imports, a bare `word >>> 3` may infer a word-valued shift
  amount through `RiscV.bitVecWordShiftRight`. Use `word >>> (3 : Nat)` when
  matching `wordShiftHOL`'s natural shift count. QueryBranch's failed elaboration
  exposed this mismatch; its checked source now states the natural count.
