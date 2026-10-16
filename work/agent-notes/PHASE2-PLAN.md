# Phase 2: finite clock proof plan

Status: dependency installation underway. No finite certificate yet.

## Strategies and sequence

1. Inspect actual pinned pass proofs, recording quantifiers and clock offsets.
   Do not infer per-pass bounds from the behaviour preservation theorem.
2. Pilot: strengthen bootstrap trace composition to expose the sum of encoded
   instruction costs. This isolates numerical clock accounting before tackling
   recursive compiler passes. Existing BootstrapTrace.full_evaluator returns
   an existential count and a clock-shift identity.
3. Strategy A: quantitative simulations for Pancake→Crep→Loop→Word→Stack→Lab→RV.
   Compose affine or otherwise monotone functions of clocks and program sizes.
   Expected effort: substantial proof engineering for each pass, especially
   loops, allocation, spilling, calls and shared-memory dispatch; estimate again
   after reading the pinned proofs. This cannot be assumed to be a small patch.
4. Strategy B (also required by A): a source work potential for gas, input,
   witness/state sizes, frame depth and table probes. Include malformed input,
   independent system-call gas, refunds and both gas pools. Expected effort:
   substantial guest invariant development, likely larger than the pilot.
5. Strategy C: investigate direct target potentials / verified cost summaries,
   avoiding quantitative versions of compiler optimization proofs. Finite-state
   existence alone is insufficient: it supplies no literal K below
   9007199254740985, and the source's traces/functions need a finite quotient proof.
6. Compose with admission and matching result, set a literal finite score and
   claim.json only after every premise is proved. Then tighten the bound.

## Proposed theorem shapes (schematic, not checked declarations)

```lean
-- Preserve the entire evaluator result under a known prefix cost.
theorem prefix_within
    (shift : ∀ clock, before (prefixCost + clock) = after clock)
    (run : ∃ clock, clock ≤ budget ∧ after clock = result) :
    ∃ clock, clock ≤ prefixCost + budget ∧ before clock = result

-- For each pass, instantiate Rel/Exec with its actual pinned definitions.
-- Rel src dst → ExecSrc src fuel result →
--   ∃ used, used ≤ passBound program fuel ∧ ExecDst dst used result'

-- The source lemma must cover exactly the Challenge premises, including
-- rejecting malformed inputs; acceptance/validity cannot be an extra premise.
-- declaredGasLimit input ≤ 200000000 →
-- sourceBehaviour input = .terminate outcome events → coveredOutcome outcome →
-- ∃ sourceClock, sourceClock ≤ sourceBound input ∧ SourceExecAt sourceClock ...
```

Every new Lean module belongs under InitECandidate/Solver. Use two-slot limited
Lake builds and print axioms for main theorems. No full baseline audit/verifier.
Record failed approaches and every open sorry in PROGRESS.md.

## Pinned pass audit (source inspection, not a new proof)

Paths below are relative to `.lake/packages/flapjack/Flapjack/`.

| Pass | Current clock relation | Numerical gap |
|---|---|---|
| Pancake → Crep | `panToCrepStateRelFiniteExact` equates initial/final clocks; `pcCompileCorrectAt` runs the target without added fuel | No extra clock in this pass. Clock counts calls/loop iterations/ticks, not all expression work. |
| Crep → Loop | `NCompileCorrect.PropertyAt`: exists `extra`, evaluate at `target.clock + extra`, relate final states | Bound `extra` for every constructor, including compiled expression/control expansion. |
| Loop → Word | `RelationsExact` equates clocks; `CompileCorrect.PropertyAt` evaluates at the original target state | No extra clock in this simulation, but generated straight-line work still costs target transitions later. |
| Word → Stack | `CompCorrect.Seq.Simulation`: exists `extraClock`, run at `target.clock + extraClock`; Seq sums the two extras | Bound call setup, spills, loops, allocation and each constructor's witness. |
| Stack → Lab | `FlattenCorrect.Statement.FlattenConcl`: exists `ck`, run or shift at `t1.clock + ck` | Must include Stack lowering/stack removal before flattening; source clock alone omits straight-line work. |
| Lab → RISC-V | `CompileCorrect.Common.CompileCorrectFor`: exists `k`, run target at `s1.clock + k` | `compileCorrect_step` uses `k' + l - 1`; bound encoder witness `l` for each instruction. |
| Bootstrap | `BootstrapAsmComposition.checked_trace_evaluator`: exists count and lower bound `code.length ≤ count` | Lower bound does not yield the needed upper bound. Each encoded step witness must be strengthened. |

Exact inspected entry files: Pancake/Proofs/PanToCrep/PcCompileCorrect.lean,
Pancake/Proofs/PanToCrep/StateRelFiniteSupport.lean,
Pancake/CrepToLoop/Proofs/NCompileCorrect/Property.lean,
Pancake/LoopToWord/Proofs/CompileCorrect/Property.lean,
Pancake/LoopToWord/Proofs/RelationsExact.lean,
Compiler/Backend/WordToStack/Proofs/CompCorrect/Seq.lean,
Compiler/Backend/StackToLab/Proofs/FlattenCorrect/Statement.lean, and
Compiler/Backend/LabToTarget/CompileCorrect/Common.lean.

The complete chain also includes frontend simplifications, Loop and Word
optimizations and register allocation, and Stack transformations. The seven
headline languages do not account for these intermediate passes.

The generic ClockBounds pilot now builds and its printed axiom sets are allowed.
TargetClock is the next pilot: a one-step halt and bound-preserving prefix
composition for evaluateTargetHOL itself. This reduces terminal off-by-one
uncertainty but does not discharge the guest-wide clock bound.

The source evaluator is noncomputable (predicate-valued domains and classical
decisions); target Evaluate.lean is explicitly noncomputable too. Direct #eval
is therefore unavailable. A measured executable mirror would require a proved
agreement theorem before its counts could certify this evaluator.

## Feasibility and effort estimates

Planning estimates, not completion promises:

- Clock bookkeeping and terminal dispatch pilot: completed in this session.
- Explicit bootstrap / encoder cost: 17 encoder constructor groups, with
  state-validity and interference assertions. A useful single instruction
  pilot is days of proof work; the full bounded encoder is roughly 1–2 weeks.
- Crep→Loop extra clocks and Word→Stack: recursive simulations with multiple
  call/handler branches; roughly 1–3 weeks each, subject to discovering reusable
  quantitative lemmas. Pan→Crep and Loop→Word need not be reproved for extra fuel.
- Stack transformations, flattening and Lab→target: roughly 2–4 weeks combined,
  provided instruction cost bounds are available. Word optimizer/allocator
  clock changes require a separate audit rather than assuming they are free.
- Guest potential/source bound: roughly 2–6+ weeks, with the highest uncertainty.
  Worst-case table probes, rollback, refunds, malformed offsets and independent
  system gas need formal invariants. Measurements do not discharge these.
- Final composition: small once quantitative hypotheses exist, but a full
  certificate check may exceed this machine's permitted build resources.

No short proof follows from the existing existential clock witnesses: their
quantifiers supply no numerical upper bound. Finite effective-input enumeration
also gives no useful bound below Yukon's limit. Retain these as explanatory
lemmas, not a route to claiming success. Direct target cost summaries remain
a possible alternative, but need machine-state invariants and coverage proofs.

Current checked TargetClock statements are concrete Lean, not pseudocode; all
three main theorem axiom lists are the permitted standard three. The next
nontrivial encoder pilot must retain the assertion witness n explicitly
(EncoderStepState currently discards it into an existential n+1).
