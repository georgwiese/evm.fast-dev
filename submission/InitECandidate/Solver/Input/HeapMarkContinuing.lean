import InitECandidate.Solver.Input.HeapScope
import InitECandidate.Solver.Input.ScopedContinuingData

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem mark_call_continuing (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (mark : BitVec 64) (name : String) (continuation : ProgHOL 64)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)))
    (code : source.code.lookup (ofString "heap_mark") = some ([], markBody, .one))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "heap_mark") [] continuation) = (none, post)) :
    1 ≤ source.clock ∧ ∃ inner,
      evaluateHOLFiniteState (bind {source with clock := source.clock - 1} name mark) continuation = (none, inner) ∧
      post = restore source name inner := by
  have positive := (CallNormal.scoped_continuing_data source post name .one (ofString "heap_mark") [] continuation normal).1
  have executed := mark_call_execute source mark name continuation heap code positive
  have joined := executed.symm.trans normal
  let ready := bind {source with clock := source.clock - 1} name mark
  have resultEq := congrArg Prod.fst joined
  have stateEq := congrArg Prod.snd joined
  exact ⟨positive, (evaluateHOLFiniteState ready continuation).2, Prod.ext resultEq rfl, stateEq.symm⟩

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.mark_call_continuing
