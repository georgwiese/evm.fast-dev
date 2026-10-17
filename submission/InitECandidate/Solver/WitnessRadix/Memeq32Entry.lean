import InitECandidate.Solver.WitnessRadix.Memeq32

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

private theorem sequence_return {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state first = (some (.returned value), post))
    (clock : post.clock ≤ state.clock) :
    evaluateHOLFiniteState state (.seq first second) = (some (.returned value), post) := by
  rw [evaluateHOLFiniteState_seq, run]
  have noIncrease : ¬ state.clock < post.clock := by omega
  simp only [fixClockHOLFinite, noIncrease, ↓reduceIte]

private theorem sequence_skip {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64)
    (run : evaluateHOLFiniteState state first = (none, state)) :
    evaluateHOLFiniteState state (.seq first second) = evaluateHOLFiniteState state second := by
  rw [evaluateHOLFiniteState_seq, run]
  have fixed : fixClockHOLFinite state ((none : Option (PanSemResultExact 64)), state) =
      (none, state) := by simp [fixClockHOLFinite]
  simp only [fixed]

/-- The whole fixed-source memeq function takes its explicit 32-byte fast
return, for both mismatches and equality. All clocks are permitted because
this path contains no loop and no call. This states the alignment-expression
and load premises explicitly; it does not assume a memeq return as a premise. -/
theorem aligned_execute {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : Fin 4 → BitVec 64)
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (aligned : eval (bind state "i" 0#64) alignmentTest = some (.val (.word 1#64)))
    (ready : ∀ check ∈ checks left right, CompareChain.Ready (bind state "i" 0#64) check) :
    evaluateHOLFiniteState state body =
      (some (.returned (.val (.word (if CompareChain.agrees (checks left right) then 1#64 else 0#64)))),
        restore state "i" (emptyLocalsHOLFinite (bind state "i" 0#64))) := by
  classical
  let loaded := bind state "i" 0#64
  let answer : ValueHOL 64 := .val (.word (if CompareChain.agrees (checks left right) then 1#64 else 0#64))
  have iNotN : ofString "i" ≠ ofString "n" := by decide
  have length' : loaded.locals.lookup (ofString "n") = some (.val (.word 32#64)) := by
    simp [loaded, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, iNotN, length]
  have fast : evaluateHOLFiniteState loaded parts.thirtyTwo =
      (some (.returned answer), emptyLocalsHOLFinite loaded) := fast_execute loaded left right ready
  have skipTwenty : evaluateHOLFiniteState loaded (.ite (sizeTest 20#64) parts.twenty .skip) =
      (none, loaded) := by
    rw [evaluateHOLFiniteState_ite]
    simp [sizeTest, localVar, evalHOLExact, toExact, length',
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have chooseThirtyTwo : evaluateHOLFiniteState loaded (.ite (sizeTest 32#64) parts.thirtyTwo .skip) =
      (some (.returned answer), emptyLocalsHOLFinite loaded) := by
    rw [evaluateHOLFiniteState_ite]
    simpa [sizeTest, localVar, evalHOLExact, toExact, length',
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using fast
  have otherUnreachable : evaluateHOLFiniteState loaded
      (.seq (.ite (sizeTest 32#64) parts.thirtyTwo .skip) parts.otherAligned) =
      (some (.returned answer), emptyLocalsHOLFinite loaded) :=
    sequence_return loaded _ _ _ answer chooseThirtyTwo (Nat.le_refl _)
  have fullAligned : evaluateHOLFiniteState loaded
      (.seq (.ite (sizeTest 20#64) parts.twenty .skip)
        (.seq (.ite (sizeTest 32#64) parts.thirtyTwo .skip) parts.otherAligned)) =
      (some (.returned answer), emptyLocalsHOLFinite loaded) := by
    rw [sequence_skip loaded _ _ skipTwenty]
    exact otherUnreachable
  have selected : evaluateHOLFiniteState loaded
      (.ite alignmentTest (.seq (.ite (sizeTest 20#64) parts.twenty .skip)
        (.seq (.ite (sizeTest 32#64) parts.thirtyTwo .skip) parts.otherAligned)) .skip) =
      (some (.returned answer), emptyLocalsHOLFinite loaded) := by
    simp only [eval] at aligned
    rw [evaluateHOLFiniteState_ite]
    simpa [loaded, aligned] using fullAligned
  have tailUnreachable := sequence_return loaded _ _ parts.tailCode answer selected (Nat.le_refl _)
  rw [body_shape, evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let result := (evaluateHOLFiniteState loaded
    (.seq (.ite alignmentTest (.seq (.ite (sizeTest 20#64) parts.twenty .skip)
      (.seq (.ite (sizeTest 32#64) parts.thirtyTwo .skip) parts.otherAligned)) .skip) parts.tailCode));
    (result.1, restore state "i" result.2)) = _
  rw [tailUnreachable]

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.aligned_execute
