# Status — update this section frequently

**Checkpoint: 2026-10-16, branch `agent/baseline-steps`, proof commit `04603be4d`.**
**The goal is NOT complete. `claim.json` still says infinity. No finite K has been proved.**
The user paused proof work to save credits. This document is a handoff, not authorization to restart expensive work. Resume proof development only when requested.

Future agent: update this checklist after each meaningful result, failed feasibility test, change of approach, and before ending a work session. Keep it understandable without reading the rest of this file. For each newly completed item, give a short evidence pointer. Keep assumptions and verification limitations visible. Do not estimate progress by counting generated files. The earlier “30%” was a low-confidence conversational estimate, not a project metric.

## Completed, with limits

- [x] Measured all 33,614 EEST records: 33,605 normal passes, 9 expected malformed passes, no failures. These are **Spike instruction counts**, not formal evaluator steps. Evidence: [Phase 1 report](work/agent-notes/PHASE1-REPORT.md).
- [x] Documented artifact hashes, Spike/formal-clock differences, synthetic inputs, zero-user-gas witness work, and a quadratic hash-table collision example. The numerical envelope remains **unproved**.
- [x] Checked an exact 23,132-step bootstrap theorem, subject to explicit baseline ROM/configuration premises.
- [x] Checked substantial quantitative compiler lemmas and complete fixed Crep/Word/Stack table checks. **The end-to-end compiler/state/oracle connection is not complete.**
- [x] Checked weighted Stack work accounting and local bounds for memzero, guarded allocation, affordable gas charging, and parts of memory expansion.
- [x] Checked the **complete** zero-expansion and nonzero/no-capacity-growth executions of `extend_memory`, under their stated entry premises. The capacity-growth case is unfinished.
- [x] Checked allocation at every initial clock, the real allocator call, its return continuation, and saved-state transfer. **Caller setup and the global invariants establishing their premises remain open.**
- [x] Committed all proof work through `04603be4d`. The evidence index contains 3,834 module hashes and 5,898 printed theorem facts; these counts are not percentages. No proof build was left running at that checkpoint.

## Next, before substantial additional proof work

- [ ] Perform the bounded feasibility review in Section 3. **Do not simply continue adding routine lemmas.**
- [ ] Write explicit theorem interfaces connecting the exact challenge premises to a bounded execution of the fixed program. Identify every missing initial-state, code, oracle, invariant, and result relation.
- [ ] Inventory all reachable work that user gas does not pay for; check malformed/oversized input, independent system gas, adversarial state/witness work, and error cleanup.
- [ ] Produce a dimensionally correct numerical budget with justified maxima and explicit unknowns; show a credible route to **K < 9,007,199,254,740,985**. The old uniform-multiplier route is too loose to adopt without new evidence.
- [ ] Run at most a few small feasibility pilots, targeting the largest uncertainty, and record a go/revise/no-go decision. No go decision has yet been earned.

## Remaining implementation and acceptance work

- [ ] Prove input/gas-reader correspondence and initialization of the global guest invariant.
- [ ] Prove a global work/clock potential covering calls, refunds, frame reuse, parsing, witnesses/state, table collisions, output, and covered failure/unwind paths.
- [ ] Complete the capacity-growth path and any other local summaries **actually required by the chosen global proof**; prove their entry premises at every use.
- [ ] Connect bounded execution through the actual compiler artifacts, bootstrap, oracle/FFI, and matching-result relation.
- [ ] Prove a literal finite K below the score cap; make `submission.K`, `claimedScore`, and `claim.json` agree; prove admission and the fixed certificate with only permitted axioms.
- [ ] Refresh policy/transport checks for the final package. The last recorded incremental policy check predates the final six allocator modules; it is not a full verification.
- [ ] Obtain final verification on a suitable, authorized host. **The user prohibited the full audit/full verifier on this machine.** No isolated finite-certificate verification has occurred.

**Next action on resumption:** complete the feasibility review and report its uncertainties before spending another long run on local proofs. **Current principal risk:** substantial checked groundwork may still fail to compose into an affordable global bound.

---

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

## 3. Cheap feasibility review: the first work to do

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

Maintain this decision record when the review is performed:

| Review item | Current answer | Evidence needed to change it |
|---|---|---|
| Decision | **Not evaluated end to end; no go decision yet** | Completed interfaces, coverage inventory, numerical budget, and targeted pilots |
| Preferred route | Weighted Named Stack accounting is a candidate | Applicable source-to-Named entry connection and a manageable global invariant |
| Uniform total Stack Work bound | Unknown | Potential proof/design covering all required work, with concrete worst-case dimensions |
| Uniform replay/base clock bound | Unknown | Whole-entry clock/rank argument, including failure/unwind paths |
| Final composed target coefficient/additive terms | Not instantiated | Thin composition theorem retaining every state/oracle/result premise |
| Numerical margin to score cap | Unknown | Exact total with no unbudgeted dominant term |
| Next review result to report | Largest unresolved assumption and the cheapest way to test it | A specific lemma, code-path analysis, or diagnostic—not a general plan to “prove more” |

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
