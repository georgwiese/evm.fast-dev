import InitECandidate.Solver.Input.CurrentHash.FixedRecordProgram
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input.CurrentHash.FixedRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem pipeline_prefix (key : MlS) (inputName : String) (steps : List Step) :
    LocalPrefix key (pipeline inputName steps .skip) := by
  induction steps with
  | nil => exact .skip
  | cons step rest ih => exact .seq (.call none _ _ (by intro name impossible; cases impossible)) ih

end InitECandidate.Solver.Input.CurrentHash.FixedRecord

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.pipeline_prefix
