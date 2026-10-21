import InitECandidate.Solver.Input.LocalLoopSummary
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- External calls retain caller locals on a real continuation and cannot
escape as return/break/continue. FFI contents and final outcomes are free. -/
theorem external_local {F : Type} (key function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) (source : PanSemStateFiniteExact 64 F) :
    LocalSummary key (.extCall function configuration configurationLength array arrayLength) source := by
  unfold LocalSummary
  rw [evaluateHOLFiniteState_extCall_source]
  repeat' first | split | simp
  change (ofExact {source.toExact with memory:=_,ffi:=_} _).locals.lookup key=source.locals.lookup key
  rw [ofExact_update_memory_ffi]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.external_local
