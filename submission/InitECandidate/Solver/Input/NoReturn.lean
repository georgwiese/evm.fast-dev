import InitECandidate.Solver.Input.CallNormal

namespace InitECandidate.Solver.Input.NoReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def Never (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (source : PanSemStateFiniteExact 64 F) (value : ValueHOL 64),
    (evaluateHOLFiniteState source program).1 ≠ some (.returned value)

theorem sequence (first second : ProgHOL 64) (front : Never first) (back : Never second) : Never (.seq first second) := by
  intro F source value
  rw [evaluateHOLFiniteState_seq_line780]
  generalize outputEq : evaluateHOLFiniteState source first = output
  obtain ⟨result, middle⟩ := output
  cases result with
  | none => exact back middle value
  | some result =>
    have known := front source value
    simpa only [outputEq] using known

theorem raise (name : MlS) (expression : ExpHOL 64) : Never (.raise name expression) := by
  intro F source value
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split <;> simp
  · simp

theorem external (name : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    Never (.extCall name configuration configurationLength array arrayLength) := by
  intro F source value
  rw [evaluateHOLFiniteState_extCall_source]
  split
  · split
    · split <;> simp
    · simp
  · simp

theorem shared_store (size : OpSize) (address expression : ExpHOL 64) : Never (.shMemStore size address expression) := by
  intro F source value
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · simp only [shMemStoreHOLExact]
    split
    · split
      · split <;> simp
      · simp
    · split
      · split <;> simp
      · simp
  · simp

end InitECandidate.Solver.Input.NoReturn

#print axioms InitECandidate.Solver.Input.NoReturn.sequence
#print axioms InitECandidate.Solver.Input.NoReturn.raise
#print axioms InitECandidate.Solver.Input.NoReturn.external
#print axioms InitECandidate.Solver.Input.NoReturn.shared_store
