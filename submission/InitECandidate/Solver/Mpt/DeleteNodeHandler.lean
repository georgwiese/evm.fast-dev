import InitECandidate.Solver.Mpt.DeleteNodeProgram
import InitECandidate.Solver.Arenas.ScratchScope
import InitECandidate.Solver.Input.NoReturnCaught

namespace InitECandidate.Solver.Mpt.DeleteNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real release/rethrow handler cannot fall through, even if its
release fails. Thus catching MptErr never manufactures an ordinary root. -/
theorem handler_stops (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (evaluateHOLFiniteState source handler).1≠none := by
  have raised (current : PanSemStateFiniteExact 64 Guest.HostMemory) :
      (evaluateHOLFiniteState current (.raise (ofString "MptErr") (localVar "e"))).1≠none:=by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split <;> simp
    · simp
  rw [handler,evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source release=output
  obtain ⟨result,target⟩:=output
  cases result with
  | none=>exact raised target
  | some stopped=>simp

theorem handler_never_returns : Input.NoReturn.Never handler := by
  apply Input.NoReturn.sequence
  · exact Input.NoReturn.ignored_call (ofString "scratch_release") releaseArguments
  · exact Input.NoReturn.raise (ofString "MptErr") (localVar "e")

theorem caught_never_returns : Input.NoReturn.Never caughtCall := by
  rw [shapes.2.2.2.2.2]
  exact Input.NoReturn.caught_destination _ _ _ _ _ _ handler_never_returns

theorem handler_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code handler 1 := by
  exact Input.ClockCost.sequence code _ _ 1 0 (Arenas.Scratch.release_call_price code installed releaseArguments)
    (Input.ClockCost.raised code (ofString "MptErr") (localVar "e"))

end InitECandidate.Solver.Mpt.DeleteNode

#print axioms InitECandidate.Solver.Mpt.DeleteNode.handler_stops
#print axioms InitECandidate.Solver.Mpt.DeleteNode.handler_never_returns
#print axioms InitECandidate.Solver.Mpt.DeleteNode.caught_never_returns
#print axioms InitECandidate.Solver.Mpt.DeleteNode.handler_price
