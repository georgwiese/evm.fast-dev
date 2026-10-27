# Finite runtime bound for the current Pancake program

Prove an explicit uniform finite bound on **formal target evaluator steps** for
the unchanged current implementation, under the fixed challenge's gas and
covered-outcome assumptions. Keep the bound reasonably tight, but **no numerical
ceiling applies**. Do not replace or optimize Pancake to meet a Yukon score
limit. A score-compatible claim or Yukon submission is not a completion requirement.

Active reference: official main `f892870c8682517186860842a3ff5f0dea1aa3eb`, after
the user-authorized rebase. Actual source: `Guest.Software.guestAst` in
`Guest/SoftwareAst.lean`. This plan supersedes the archived historical plans.

## Scope and completion criteria

- Follow `InitE.Certificate` in `InitE/Challenge.lean`: every mathematical input
  byte list with declared gas at most 200,000,000, conditional on actual covered
  source termination. Derive extra validity, ownership, gas, allocation and
  helper-entry conditions from actual execution; do not assume future success.
- Preserve source, semantics, ROM and fixed proofs. Retain accepting output
  matching and covered rejection/trap cases from the actual observation relation.
- A source call/loop clock bound omits straight-line work. An input-dependent
  finite halt witness already exists at infinity. Neither is the requested
  uniform target-step bound. Evaluate the final proved expression exactly and
  review dominant slack; produce the quantitative theorem and checked evidence.
- Keep `claim.json` at infinity until an actual finite certificate justifies
  changing it; do not alter it merely to fit a score format.
- Targeted Lean checks are not isolated comparator/axiom audit/kernel replay.
  Do not claim final verification without a successful run. Existing restrictions
  on running the full verifier on this machine persist.

Read `AGENTS.md`, `docs/CHALLENGE.md`, `docs/SUBMISSIONS.md`, `docs/TESTING.md`
and actual contract/semantics as needed. **Do not read `CLAUDE.md`.** Some prose
arena descriptions are stale; use the fixed definitions.

## Current status — 2026-10-27

**No global finite target K yet**; claim remains infinity, no complete verifier
run claimed. Best overall effort estimate: **40%, range 30–50%**, relative to
current main. Module counts are bookkeeping, not completion percentages. The
earlier speculative K guess, 10^14–10^18, is not proved or a target ceiling.

Checked against the current Software AST:

- Actual installed-code/declaration-pass/evaluation-preservation interfaces;
  generic helpers shed old host/map/hash dependencies.
- Actual continuing shared reads derive presence, replies and scalar values.
  The raw gas field is at most 200,000,000 after both canonical container
  offsets derive at the genuine returning decoder;
  transporting the raw bound to its later actual payload gas load remains open.
- Whole header precheck: every outcome costs at most **85 body /86 caller source
  ticks**. Its actual signed small-count offset loops include failed accesses
  and decoder exceptions.
- Whole `input_blob`: every outcome costs at most **134,217,728 body /134,217,729
  caller source ticks**. The stride-eight loop costs `(length + 7 - i)/8`;
  length comes from the actual load and passing guard. Allocation/trap failures
  are included without future readability, room or store-success premises.
- Actual normal copy-loop execution now yields its exact state, observed host
  presence/destination mappings, input-byte correspondence and an exact frame
  outside copied words. This composes through the real i/w scopes and tuple
  return. Actual continuing length reads identify input.length modulo 2^64,
  deriving header presence even for word-overflowing mathematical list sizes.
  BlobReached now joins the actual allocator, complete body and returning caller:
  it derives real room, the encoded-length bound, tuple binding, byte image,
  exact heap update, paid clocks and protected-word frame. Initial heap cursor,
  alignment/endian/oracle invariants still need derivation from actual main.
- Allocator/trap/input catalogues use actual Software function entries 2/0/24.
  Shared local-summary composition and fixed counter increments are generic.
- The actual memzero body/ignored call cannot continue from an aligned clear of
  at least32bytes below sourceBase. The genuine scratch allocation derives its
  room/rounded pointer/alignment before this clear. Current msg_new_scratch and
  frame_new (including both real cursor snapshots) cannot return under ordered
  bounded arena cursors and the actual domain. These are conditional control
  facts, not yet whole-path exclusion or covered-outcome classification.
- Current main entry and its genuine mem_init prefix now build: main function
  index812, 67 scalar declaration globals, heap=@base, scratch=2701127680 and
  frame_mem=2688618496. Entry.base comes from the actual source declaration
  frame. Every actual terminating source behavior reaches this computed prefix.
- CurrentStartup now checks the actual closed startup/decoder/result-writer call
  graph (46 helpers), preserving both arena globals on every outcome. Prefix
  reconstructs the literal13initializer calls after mem_init and proves their
  exact evaluation cut: each actual termination either stops inside that prefix
  or reaches the real following main state with both initialized cursors retained.
  This is not an initializer runtime bound or a proof that every input reaches
  the suffix. DecoderPrefix now reconstructs the real six lexical actions through
  the caught decoder call and joins their actual continuation/early-stop cut to
  whole source observations. It retains live out/z32/si/err_code bindings and
  preserves the full nonlocal observation on stopped paths. DecoderReturn proves
  the real rejection handler cannot fall through and extracts the actual checked
  scalar decoder return from a completed prefix. NormalHost now checks host
  preservation at real returns for all28startup helpers, including a vacuous
  trap-return case. HostPrefix derives original host input, byte order, source
  oracle and arenas through actual startup/setup into the real decoder entry.
  AllocationChecked derives bounded/aligned post-cursors from actual returns
  without an initial heap bound or assumed heap cell. DecoderHeap applies this
  to main's last setup allocation and carries it through memzero/declarations.
  ReadHostEffects now proves all-outcome host-byte preservation under the real
  source oracle; precheck/callee proofs retain the heap and arenas as well.
  DecoderInput joins the actual precheck and input_blob call to the live copied
  tuple/image. StatelessEntry derives real p/len parameters, image and next heap
  at the actual stateless body entry. MainCopiedInput reaches this from complete
  source observations, preserving startup/decoder stops and main's true si binding.
  HostState now retains exception declarations, shared domain and source base too.
  EarlyWorkspace now checks the actual SHA/Keccak/first SSZ allocations and
  the zero-hash guard. Main starts SSZ with a 720-byte heap advance and allocates
  its64-byte offset buffer at **0xa10002f0 (2701132528)**. WorkspacePointer proves
  that pointer survives all later actual startup calls; OffsetsFrame checks the
  closed43-helper suffix/decoder/output graph. This is pointer preservation,
  not memory-content preservation. NormalHeap now checks real returning effects
  for the26-helper startup closure. EvmHeap derives the real snapshot, preserves
  its local mark through35prefix actions, and proves the actual release restores
  the saved frontier; it does not assume release is monotone. StartupHeap carries
  the post-SSZ lower frontier2701134640through all remaining startup/setup/precheck
  work. StatelessEntry retains the observed input pointer cell and nonheap global
  frame. SeparatedInput joins this to complete source observations: at the actual
  stateless entry, ssz_offs=2701132528, input pointer≥2701134640and its entire
  bounded copied allocation is in range. Every64-byte workspace address is below
  that pointer. Startup/decoder stopped paths remain explicit; image lifetime
  through later decoder writes remains open. CopiedHeap additionally derives
  that the stateless-entry heap lies beyond pointer+encodedlength+8, including
  real alignment rounding. CanonicalHeader now derives the actual schema bytes,
  encodedlength≥18and first container offset=16 from the real returned decoder.
  HeaderAfterTrace reaches the actual first-container continuation at its original
  clock with paid≤4derived from enclosing execution and input bytes intact through
  the first two workspace stores and validator. The witness offset is also
  derived between16and encodedlength−2. AllocationFrontier now derives the exact real scoped
  allocation return and caller state. RequestCut exposes the live six actions
  through the stateless record's chain-ID store; InputImageFrame retains copied
  bytes across the observed scalar store without assuming its value read or
  destination mapping. RecordEntry joins this to the whole-main stateless run,
  retaining an aligned96-byte record beyond input+length+8and actual request-length
  guard continuation. RequestPositions now derives real np=pointer+18and
  nlen=witness−16bindings from actual loads/scopes. GuardActual derives nlen≥44,
  encodedlength≥62and the actual request body continuation without extra funding.
  CanonicalRequest joins the real three workspace stores/validator, deriving
  offset44and actual offset ordering. Both16/44canonical guards now connect the
  declared gas limit to original le64(input,474)≤200000000. This is the raw input
  field, not yet its actual payload load/store. PayloadEntry now joins the real
  payload call and its length guard: p=input+62, slice≥540, encodedlength≥602,
  contained slice, original byte image, actual code/exception/domain/endian and
  post-copy heap frontier at the real payload callee. The passing guard and body
  return are extracted at their original clocks; no future funding is supplied.
  PayloadProgram/Gas now select the actual Software payload AST and explicit
  minimal header/gas imports. PayloadCut now reconstructs the real seven actions
  through alloc136, pointer/length stores and four offset loads. Allocation room,
  current pl binding and lower frontier derive from actual execution.
  PayloadHeaderImage preserves copied bytes through both real header stores;
  PayloadWorkspace joins this back to main-derived payload entry with current
  metadata, p/len/pl bindings, separate136-byte record and actual offset body.
  PayloadOffsetsLocals derives all four offset locals from the original copied
  input and actual declarations. PayloadValidated now joins the real four
  workspace stores/validator, deriving extra offset540and all four ordering/range
  guards, preserving input bytes and the reusable PayloadWorkspace.Context.
  Extra-data guard, array writes and later gas store remain open.
- CallPrefix drops the unrelated ClockCostScopeLocals umbrella; its transitive
  Solver closure falls from155to7modules. The trace closure falls158to10.
  HeapScope now imports actual Software AST and minimal generic return/state
  helpers, reducing its Solver dependency closure151to9. NoReturnScoped reuses
  the shared ignored-call rule instead of declaring a duplicate theorem.
  HeapInput and AllocatedArena split byte-image/geometry facts from unrelated
  historical copy/zero execution. HeapFrame closure82to29, ScalarProgram51to12,
  HeaderEntryNormal114to65and HeaderAfterNormal111to62. Header syntax uses the
  actual Software decoder; raw le32 bounds use mathematical bytes directly.
  Existing clock-only interfaces are retained as projections of the stronger
  stopped-state classification. CaughtAssignedStops and NoFallthrough also use
  their actual minimal imports. These are proof dependency changes, not changes
  to the fixed guest or semantics.
- Replacement implementation/closed proofs/generators/harness were removed
  earlier. Another 65 closed stale generated modules were removed after rebase.
  Other old-program proofs remain historical until their current dependencies
  and statements pass real checks.

Latest successful closure: `current-payload-validated-v2.log`, 1,263 jobs,
permitted printed axioms only, 9.83 seconds, MaxRSS 1,877,572 KiB.
Historical/current index: 7,915 modules /15,727 facts; 375 modules carry the
current dependency reference. Incremental package policy passes at64,719entries/
2,481,733,835bytes; historical copy/zero execution wrappers are not revalidated.
These checks are not full verification.

## Remaining plan

- [x] Rebase onto latest official main; preserve old checkpoint and stashes.
- [x] Remove replacement implementation/unused closure and closed stale generated
  modules; retain shared helpers needed by actual current-program proofs.
- [x] Retarget core code installation, actual shared reads, current header cost
  and complete input-copy cost; clean their stale dependencies.
- [x] Join actual main/startup/setup/precheck/input_blob to the copied image,
  real pointer/length parameters and metadata at the stateless decoder entry.
- [ ] Finish workspace geometry: the actual ssz_offs address/64-byte allocation
  and later startup pointer frame are proved. Persistent heap ordering through
  actual startup/setup/precheck, including the real heap mark/release, now derives
  workspace/input separation at genuine stateless entry. Preserve the copied
  image through remaining decoding writes; the first two workspace stores,
  validator and fresh stateless record chain-ID store now pass. Derive actual
  request-length bounds/offsets now pass; finish the payload/gas load join.
  Port remaining HostLength/HostWords/HostGas callers; old unconditional backing
  claims are stale. Close actual offset guards/decoded layouts/gas.
- [ ] Derive current main initialization, allocation geometry, memory ownership
  and input/heap/scratch lifetimes. Input maximum is 1,073,741,808 bytes; allocation
  ceiling is 2,952,790,016. Scratch is below sourceBase and outside compiler ordinary
  memory; analyze actual covered execution rather than assuming it excludes all
  valid inputs. Retain arbitrary mathematical list sizes, including word wrap.
  Prioritize checking the earliest actual scratch access and its covered-outcome
  consequences before expanding the map/crypto migration. CurrentDomain now
  proves every ordinary address is at least sourceBase and that scalar stores
  below it fail immediately; no whole-path unreachability is claimed yet.
  The initial arena cursors now follow from the real main/mem_init prefix.
  Their transport through the13startup calls now has an exact whole-main cut.
  The actual six-action decoder cut now retains its lexical scopes and both
  arena globals; successful continuation derives the actual scalar decoder return.
  Host/heap input prerequisites now derive at the genuine decoder body entry.
  The heap invariant is bootstrapped by the actual last setup allocation's second
  guard and alignment mask; an exact normal-startup allocation total is not needed
  for that invariant. The real precheck/copy/stateless-entry join now passes.
  Real workspace/input separation now derives at the genuine stateless entry.
  Prove image lifetime through decoder stores before transporting parsed
  offsets/gas through workspace writes. Classify genuine scratch helper outcomes. NoReturn alone does not rule out covered terminal
  FFI outcomes, so do not discard later EVM/map obligations on that basis.
  AllocationArithmetic/Normal/Call/CallNormal and the Expected/NormalExpected/
  GlobalExecution/GlobalNormal/ProgramPrefix/InitializerAllocations interfaces
  now use the actual 2,952,790,016 ceiling. RoundedExpected is split from the
  prefix umbrella; GlobalNormal dependencies fall66to23 and initializer allocation
  dependencies82to43. InitializerNormal derives real prefix room and states from
  observed returns. Remaining Local variants and old callers still need migration.
- [ ] Bound actual Patricia maps and software cryptography. Reuse unchanged
  proofs only after checking current code, indices and dependencies; obsolete
  table/accelerator contracts do not discharge the new obligations.
- [ ] Complete serialization/traversal/hash/root and persistent graph ownership,
  EVM/gas/charge/refund/child calls, journal/rollback, output and covered failure/
  unwind paths. Derive global event/resource totals and genuine helper entries.
- [ ] Regenerate/check current compiler static facts. Compose weighted source
  work/clocks through the actual compilation, bootstrap/oracles and target
  evaluator. Evaluate a literal finite K and remove dominant unjustified slack.
- [ ] Final cleanup of remaining obsolete scaffolding/proof branches; refresh
  retained dependency/evidence checks and applicable final validation. Do not
  substitute a conditional interface for a closed global obligation.

## Working rules and recovery

- Continue autonomously; no milestone approval stops. **Push to georg after
  every commit**, using the existing credential helper without printing tokens.
  Do not run Yukon submission or merge a PR.
- Check account usage regularly with `/tmp/init-e-account-usage.py`. User means
  account usage-limit resets. Last check: 11% weekly used, zero reset credits,
  ordinary usage allowed.
- One selected build at a time, two Lean slots, artifact cache disabled,
  **8 GiB whole-host used-memory stop guard**. Stop if disk exceeds 85%. Poll
  existing live builds rather than restarting. No unqualified whole build,
  baseline audit or Solution build merely to check a helper.
- Permitted axioms: propext, Classical.choice, Quot.sound only. No proof holes,
  native axioms, fixed-source changes or dependency updates. Only Solver,
  Solution and claim survive Yukon overlays. Preserve pinned dependencies.
- Index terminal successful logs only, matching unchanged checked source.
  Use record-proof-build.py, original-plan-inventory.py, incremental
  check-solver-policy.py and git diff --check for coherent checkpoints.
- Five unfinished pre-rebase RLP files remain untracked; preserve until current
  dependency checks pass. They are not current proof successes.
- Old head 20080445b4247372ec639a2133558441111cdf54 is preserved locally and on
  georg as codex/pre-upstream-rebase-20261027. Restored RLP stash
  0d43ada2a12374ec0432fd3f46edfef512bdce99 is retained.

Current records: [PROGRESS](work/agent-notes/PROGRESS.md),
[proof index](work/agent-notes/proof-checks.json),
[inventory](work/agent-notes/original-plan-inventory.json),
[rebase notes](work/agent-notes/UPSTREAM-REBASE-20261027.md).

The previous 930 KB task document and 1.17 MB progress document are preserved
byte-for-byte as [task history](work/agent-notes/BOUND-HISTORY-PRE-CLEANUP-20261027.md)
and [progress history](work/agent-notes/PROGRESS-HISTORY-PRE-CLEANUP-20261027.md),
with hashes in [archive manifest](work/agent-notes/rebase-cleanup-history.json).
Their old program indices, numerical gates, plans and conflicting operational
instructions are historical; later user instructions and this plan govern.
