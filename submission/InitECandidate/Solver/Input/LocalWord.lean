import InitECandidate.Solver.PanState
import Guest.Model

/-! Generic local scalar lookup, retaining its historical namespace. -/
namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem local_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64)
    (present : source.locals.lookup (ofString name)=some (.val (.word word))) :
    eval source (localVar name)=some (.val (.word word)) := by
  simpa [eval,localVar,evalHOLExact,toExact] using present

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.local_word
