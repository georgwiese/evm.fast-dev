# Phase 2: finite clock proof plan

Status: Phase 1 measurements and the generic bounded Lab-to-RISC-V simulation
and quantitative Stack flattening are checked under explicit code/size
invariants. Fixed-layout checks remain in progress. No finite certificate yet; the submission still claims infinity.

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
| Lab → RISC-V | `CompileCorrect.Common.CompileCorrectFor`: exists `k`, run target at `s1.clock + k` | Solver now checks the full recursive bound for static code with bounded encoded line lengths. Fixed-program layout premises and earlier clocks remain to be certified. |
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
- Explicit bootstrap / encoder cost: complete. All 17 constructor groups have
  a checked ceiling of 16 native transitions, retaining state validity,
  interference and both assertion predicates. The earlier 1–2 week estimate
  was too pessimistic: systematic witness retention built 30 component modules
  and the aggregate theorem in 1m06s after dependencies were available.
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
3. Checked RiscVEvaluatorCosts, SupportedCosts and BootstrapCost cover the
   bootstrap instruction forms and compose their exact 23,132-step sum.
   BootstrapStartup now discharges the actual initial-state checks and identifies
   installedAsm as the endpoint, for any submission with the baseline ROM,
   anchor, ordinary FFI count and nonwrapping MMIO offsets.
4. Lab-to-target recursive cost transfer is checked under explicit static-code
   and line-size premises. Certify those premises for all fixed padded sections,
   then propagate quantitative bounds through preceding passes. Also attempt
   a direct target cost potential for guest loops, alongside the source
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
specializations and their bootstrap assembly are now checked. BootstrapCost is
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
lightweight cost module's candidate closure has only 16 modules. External
Mathlib imports still have a substantial first-build cost.

## Checked bootstrap milestone

BootstrapEncoding.bytes_match proves that the 40 ASM blocks encode to the
submitted ROM's first 208 bytes. BootstrapCost.exact_total proves the weighted
trace sum is 23,132. BootstrapCost.evaluator proves an exact prefix of that
length for evaluateTargetHOL, conditional on WeightedTrace.Checked, Guards and
the initial ASM/machine relation. All main theorem axiom sets are recorded in
proof-checks.json; none exceeds the permitted three. There are no open sorrys.

Those startup checks are now discharged in BootstrapStartup. The fixed
BootstrapStraightLine and BootstrapCopyTrace proofs avoid ArtifactFacts, so they
can be reused within this machine's limits. BootstrapTailChecks adapts the 32
tail instruction checks to closed PC/domain regions; BootstrapRegion derives
FFI dispatch guards from them. BootstrapMachine proves the initial relation for
arbitrary input, and BootstrapStartup.evaluator composes the exact prefix:

```lean
-- Parameters: sub.code = InitECandidate.code, sub.anchorPc = nativePc,
-- sub.first = 20, and each nativePc + MMIO entry offset < 2^64.
∃ post,
  (∀ clock, evaluateTargetHOL sub.machineConfig io (23132 + clock)
    (sub.initialState input) =
      evaluateTargetHOL sub.machineConfig io clock post) ∧
  targetStateRel riscvTarget installedAsm post
```

This is a checked theorem, with no supplied execution/trace/guard premises.
The small metadata equalities remain explicit parameters; this development
does not import or rebuild baselineSubmission's full artifact closure.

The next native-body layer is now partly checked: full encoder coverage and
padded compiler lines, described below. Bounded control-flow/library summaries
or the source gas/input potential plus quantitative compiler transfer remain
necessary. No current theorem proves a finite certificate; claim.json and
Solution.lean remain unchanged.

## Complete encoder and Lab line bounds

BoundedEncoder.encoder checks, for every HolAsm constructor and the original
asmStep/targetStateRel premises:

```lean
∃ n, n + 1 ≤ 16 ∧ EncoderClock.EncoderAt riscvTarget s1 s2 ms i n
```

The ceiling is deliberately loose. Branch outcomes may choose different n;
therefore BoundedTrace.evaluator composes existential per-state costs rather
than assuming a fixed counter per instruction. A checked ordinary trace of m
ASM operations yields a real evaluateTargetHOL prefix with m <= count <= 16*m,
with the final state relation and every remaining clock preserved.

EncoderBound.Contract/step make this interface polymorphic for compiler proofs;
BoundedStep.contract supplies the actual RISC-V contract at bound=16.
NopCost.evaluateNopSteps proves n NOPs cost at most bound*n.
NopCost.asmStepImpEvaluateStepNop proves a non-call padded line costs at most
bound*(bytes.length+1), retaining the original memory/frame/control premises.
LabCost.stepOfLine, stepNopOfLineMem and stepNopOfLine lift those bounds through
the existing compiler state relation and fetched-line encoding checks. They
also preserve findNextInterference, needed by oracleTie_step.

LabBound now strengthens CompileCorrectFor and compileCorrect_step, adapts
Asm/Control/Cbw/ShareMem/CallFfi, and assembles strong induction on the source
clock. Terminal and returning FFI dispatch are included. Install can change
target code, so the new theorem explicitly assumes no source position invokes
it. It does not silently reuse a line ceiling across installation or assign
dynamic installation a guessed cost.

The checked RISC-V conclusion is:

```lean
-- Full original oracleTie, evaluate, non-error and stateRel premises;
-- plus mc.target = riscvTarget, LineBound code limit, NoInstall source.code.
∃ count post, count ≤ (16 * (limit + 1) + 2) * source.clock ∧
  evaluateTargetHOL mc source.ffi count ms = (res, post, finalSource.ffi)
```

LineBound is an upper bound on each adjacent posVal displacement. Layout proves
it from bounded individual line lengths and zero-width labels; it also proves
NoInstall from line syntax and transfers it along codeSimilar. CheckLayout is
a computable Boolean check with a kernel-proved specification covering both
premises. PaddedPilot.padded64_fits certifies one actual fixed target section
at limit=24 using ordinary decide and only propext.

The text scan of all 832 Padded literals found 205,014 encoded lines / 904,196
bytes, maximum length 24 and no Install token. This suggests multiplier 402,
but the whole-program facts are not yet kernel-certified. The fixed Padded
imports have a 5,587-module / 471 MB candidate source closure. The first-section
pilot took 1m53s and peak child RSS 4.0 GiB. Test a largest section before the
complete layout build, and keep disk/RAM monitoring in place.

The multiplier 402 is a deliberately loose intermediate bound, not a claim
that the final K will fit Yukon's cap. If composing it with adversarial work
potentials exceeds the cap, retain encoded-length/one-step-NOP costs rather
than the current uniform 16-per-operation padding ceiling. That refinement
must be proved; no tighter multiplier is currently claimed.

This removes the recursive quantitative gap at the final compiler stage for
the stated static-code class. Fixed-program instantiation is still pending.
It does not bound the guest's Lab clock from gas/input or the preceding passes'
clock expansion. Those remain the dominant unfinished certificate obligations.

## Complete fixed-layout build in progress

PaddedLarge certifies the largest fixed section, 713, at limit 24. Build wall
time including dependencies: 9m25.48s, peak child RSS 4.08 GiB, peak whole-host
used memory 7.13 GiB, disk at most 47%; only propext in the main theorem.

The generator now emits all section checks and combines them in 54 chunks.
The exact metadata list order/append tree is retained, using the original
Padded declarations. The later equality to Metadata.paddedProgram remains an
artifact-integration obligation; no compiler-output equality is assumed.
StaticTarget transfers NoInstall through the existing full stateRel, and the
pending PaddedRiscV theorem specializes the checked simulation to multiplier
402 without an extra source-static premise.

The full layout build runs sequential chunk requests inside one four-slot
limiter, with host-memory >24 GiB and disk >85% stop guards. Slot increase is
supported by the measured largest-section pilot. Generated modules are not
counted as checked until their Lean builds and printed axiom sets succeed.
This is the 5,587-module padded-section closure, not the prohibited full audit
or baseline verifier.

For the next Stack-to-Lab flattening stage, the inspected proof spends extra
clock on straight-line instructions and conditional/join jumps; calls and
loop reentry decrease source clock. A promising strengthening bounds extra
clock by a constant times structural program-node count plus a maximum callee
body size times spent source clock. Use a new node count ignoring literal and
register magnitudes: Lean sizeOf includes those operands. Preserve final
source-clock information so sequential costs telescope. Static source code
(no Install) and a bound on all callee bodies must be maintained across calls.
This invariant is proposed only; neither the multiplier nor its preservation
is yet proved.

## Checked Stack flattening pilot

FlattenBound.Common defines operand-independent syntax node counts and the
extra-clock budget `4*((limit+1)*(initial-final)+nodes program)`. The Seq
arithmetic lemma telescopes spent clocks. Leaves checks the actual exposed
witnesses for Skip, Halt, Inst and Tick; Control checks numerical composition
and the Seq rule from bounded simulations of its actual sub-runs. All eight
printed main theorem axiom sets are permitted. This does not establish the
budget for arbitrary programs: remaining cases, call/loop recursion, static
code preservation and callee/body bounds still need proofs.

A uniform maximum-body multiplier may be too loose for the final score cap.
Keep syntax/spent-clock accounting explicit and retain per-function charges
if later composition exceeds the cap; no feasible final K is inferred from
this pilot's arithmetic.

## Recursive Stack flattening checked

The pilot budget now holds for every constructor under `ProgramOk M p` and
`StateOk M s`. ProgramOk bounds structural nodes and excludes Install. StateOk
requires ProgramOk for every installed body and every possible compile-oracle
extension. `stateOk_evaluate` derives preservation from the existing exact
code/oracle-history theorem; the compile-oracle premise is explicit and still
needs discharge for the guest's initial state.

`FlattenBound.Assembly.boundedPropAll` has checked type:

```lean
ProgramOk limit prog → StateOk limit source → BoundedProp limit prog source
```

BoundedProp retains all original flattening hypotheses and its exact simulation
conclusion, with extra clock at most
`4*((limit+1)*(source.clock-finalSource.clock)+nodes prog)`.
This covers Seq, six conditional flattenings, loops, direct/raw/tail calls,
returning calls and handlers, FFI, shared memory, and all leaves. Install is
excluded by ProgramOk; guarded stack/store/allocation operations are impossible
under the original flattening state relation. Calls and loop reentry discharge
the original clock/size induction measure, not an assumed recursion bound.

`FlattenBound.WholeCall.boundedCallCorrect` also passes: whole-entry Lab
execution uses initial clock `source.clock-1+ck` with
`ck ≤ 4*((limit+1)*source.clock+2*limit)`. It retains the original result class,
FFI and return-to-halting-procedure premise, including timeouts. The second
body in a return-to-halt run consumes no source clock by that original premise;
its syntax cost is explicitly included. All printed axioms are permitted.

Next obligations: bound the actual removed Stack bodies and compile oracle;
bridge the precise fixed artifacts/initial states; quantify StackRemove,
StackAlloc and earlier passes; prove the source gas/input work potential.
The uniform maximum-body budget may exceed the score cap after composition.
It is a checked intermediate bound, not an asserted feasible final K.

StackRemove inspection suggests most instructions and successful stack-space
operations use zero extra source clock; allocation failure uses one and halts.
Its recursive arbitrary-count allocation proof propagates the final witness
without adding one per chunk. Expose this bound next, retaining its guards and
full state relation. This observation is source inspection until a new proof
build succeeds; it does not yet establish a whole-pass bound.

## Stack-removal pilot: zero clocks for continuing runs

StackRemoveBound.Allocation now checks the arbitrary-count recursive allocator:
extra clock <= 1, and extra clock = 0 whenever the requested space is available.
StackRemoveBound.Free checks extra clock = 0 for arbitrary-count release.
The original arithmetic/overflow guards and complete post-state relation remain.
No cost is assigned per chunk: successful chunks consume no Stack clock.

Space expresses the constructor budget as `resultBudget result`, equal to 1
for a Halt result and 0 otherwise. Seq has been checked with that budget: its
continuing first run contributes zero, so the total stays at resultBudget.
Atoms, Control, Instructions, Locations, CodeBufferWrite and ShMemOp also pass.
This suggests a <=1 whole-pass bound for the guest's static program class,
but recursive calls, remaining constructors and invariant closure are unfinished.

A reproducible text scan of the 826 Raw and 826 Alloc procedure files finds
zero StoreConsts, Install and heap Alloc constructors, and 9,933 StackAlloc
occurrences in each stage. The 826 Removed files contain none of those four.
This is not kernel certification and excludes the small runtime procedures.
StoreConsts must not be silently ignored: its generic proof introduces a
copyLoop allowance that depends on bitmap-driven copying. Either certify its
absence for the complete installed code/oracle or bound that loop separately.

Conditional and loop rules now also pass with the same result budget.
Next: finish remaining leaves and bounded call cases;
assemble induction under explicit exclusion of StoreConsts and Install,
preserving that condition through code/oracle history. Then certify actual
fixed-code invariants, accounting for small runtime procedures as well as
numbered procedure modules. StackAlloc (the earlier heap-lowering pass),
WordToStack, CrepToLoop and the guest-wide source potential remain separate.

## Recursive Stack removal checked

StackRemoveBound.Assembly.compCorrect now closes all constructor cases under
`eligible`-style `supported program = true` and `StateSafe source` premises.
The predicate excludes Install and StoreConsts recursively; StateSafe checks
installed bodies and every compile-oracle extension. Evaluation preservation
uses the imported exact code/oracle-history theorem. Heap Alloc is impossible
under this pass's original state relation; its original error guard remains.

The actual compiled execution has extra clock <= resultBudget result, where
resultBudget is 1 for Halt and 0 for every other result. Seq, loop reentry,
return continuations and exception handlers preserve zero extra clock on their
continuing prefix, so the bound does not grow with recursion or input length.
Every memory/register/stack/FFI guard and full original postrelation remains.
All printed main theorem axioms are permitted.

Entry.entrySimulation specializes this to the whole entry call at any chosen
source clock. Entry.initializedEntry additionally prefixes the actual
initializer execution, using existing InitClock.evaluateInitCodeClock; the
initializer uses no Stack clock. This theorem still requires the initializer
run and the full relation it establishes. It does not assume or certify that
the fixed guest satisfies its preconditions.

Next is StackAlloc (heap-allocation lowering). Its 25 nonrecursive cases expose
zero witnesses in the source proofs. The new ZeroGoal retains the exact target
override, original Pre and Post and adds ck=0. A recursive theorem should cover
program/code/oracle syntax excluding Alloc, StoreConsts and Install; the fixed
Raw text scan supports testing this class but does not discharge it. Preserve
those restrictions at actual recursive evaluation sites. Calls remain necessary
even if the compiler leaves most eligible syntax unchanged, because target code,
flags, registers and compiler/oracle fields change. No blanket identity proof
for the evaluator is being assumed.
