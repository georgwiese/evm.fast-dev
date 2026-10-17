import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A successful binary word operation on two locals derives both scalar
bindings, rather than assuming the source program's declarations succeeded. -/
theorem operation_local_words {F : Type} (source : PanSemStateFiniteExact 64 F)
    (left right : String) (operation : BinOp) (value : ValueHOL 64)
    (read : eval source (.op operation [localVar left, localVar right]) = some value) :
    ∃ a b : BitVec 64,
      source.locals.lookup (ofString left) = some (.val (.word a)) ∧
      source.locals.lookup (ofString right) = some (.val (.word b)) := by
  classical
  simp only [eval, evalHOLExact, evalListHOLExact, localVar, toExact] at read
  cases first : source.locals.lookup (ofString left) with
  | none => simp [first] at read
  | some firstValue =>
    cases second : source.locals.lookup (ofString right) with
    | none => simp [second] at read
    | some secondValue =>
      cases firstValue with
      | rStruct fields => simp [first, second, valueIsWord] at read
      | nStruct name fields => simp [first, second, valueIsWord] at read
      | val firstPayload =>
        cases firstPayload with
        | word a =>
          cases secondValue with
          | rStruct fields => simp [first, second, valueIsWord] at read
          | nStruct name fields => simp [first, second, valueIsWord] at read
          | val secondPayload =>
            cases secondPayload with
            | word b => exact ⟨a, b, rfl, rfl⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.operation_local_words
