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
    (shift : ∀ clock, before (prefix + clock) = after clock)
    (run : ∃ clock, clock ≤ budget ∧ after clock = result) :
    ∃ clock, clock ≤ prefix + budget ∧ before clock = result

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
