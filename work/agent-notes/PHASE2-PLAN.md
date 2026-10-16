# Phase 2: finite clock proof plan

Status: Phase 1 measurements complete. Dependencies installed; seven cost/bookkeeping
modules checked. No finite certificate yet; the submission still claims infinity.

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
TargetClock is also checked: a one-step halt and bound-preserving prefix
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
  state-validity and interference assertions. Skip, Memory and Loc were specialized successfully in this session, so
  the earlier days-per-pilot estimate was too pessimistic. Their existing proofs
  construct explicit small witnesses; retaining them is a tractable local edit.
  Branches, variable-width constants and composition remain; estimate 1–3 days
  for bootstrap coverage and 1–2 weeks for the full encoder, subject to checking.
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
three main theorem axiom lists are the permitted standard three. The checked SkipCost, MemoryCost and LocCost modules retain the assertion
witness explicitly: respectively n=0, n=0, n=1, corresponding to 1, 1 and 2
native transitions. Each derives fetch/decode/execution from asmStep and the
initial relation, and retains both assertion predicates and all interference
environments. Main theorem axiom lists contain only the standard three.
EncoderStepState currently discards this counter into an existential n+1;
EncoderClock now carries it through the actual evaluator bridge;
RiscVEvaluatorCosts checks the three corresponding exact evaluator prefixes.


## Current implementation order and proof obligations

1. Checked ClockBounds, TargetClock, SkipCost, MemoryCost and LocCost. No open
   sorry. Exact native costs do not themselves assert evaluator dispatch costs.
2. Checked EncoderClock.evaluator_exact: an exposed counter n yields a shift of
   n+1 in evaluateTargetHOL, retaining interference and findNextInterference.
   This adapts the pinned proof without changing the dependency.
3. Checked RiscVEvaluatorCosts specializes the three constructors. Extend exact encoder
   witnesses for constants, integer binops and bootstrap branches. Compose a
   weighted trace and prove the current bootstrap's numerical cost.
4. Attempt a direct target cost potential for guest loops, alongside the source
   potential route. Prefer reusable summaries of library functions over a full
   quantitative reproof of all optimization passes if this avoids duplicated
   invariants. This is an approach choice, not a claim that such summaries exist.
5. Prove gas/input/state-size invariants and termination bounds. Measurements
   revealed zero-gas witness work and quadratic collision chains; a gas-only
   potential is infeasible. A coefficient inferred from EEST is also infeasible.
6. Only after those obligations, compose the finite certificate and update K.

The numerical planning envelope in PHASE1-REPORT is deliberately unproved.
Its arithmetic fits under the score cap, but neither the affine shape nor its
coefficients have a guest-wide justification. A source clock bound and compiler
cost transfer remain necessary; none is supplied by the pilot assumptions.

## Trace-composition progress

WeightedTrace.evaluator now proves the exact sum of exposed encoder counters
plus one per ASM operation, preserving the actual evaluator's quiet prefix.
ConstCost covers all U64 constants (at most six native instructions); Binop
Reg/Imm and LSL immediate costs are checked at one step. Near branch/jump
specializations and their bootstrap assembly are building. BootstrapCost is
explicitly conditional on the local ASM validity and evaluator guards; checking
its numerical sum alone will not prove startup from the challenge initial state.
The lightweight layout avoids the fixed BootstrapProgram module's broad image
and compiler imports; equality to the literal prefix is a separate obligation.

The fixed BootstrapTrace import is not a safe shortcut on this machine: a static
import traversal reaches 47,123 candidate modules (1.82 GB source) via ArtifactFacts.
That approaches the prohibited full baseline build. Do not build it merely to
reuse the initial-state guards. Instead, specialize/reprove the required guards
using the fixed literal prefix and a small memory-domain interface under Solver;
connect that interface to the actual machine configuration separately. The new
lightweight cost module's candidate closure has only 15 modules. External
Mathlib imports still have a substantial first-build cost.
