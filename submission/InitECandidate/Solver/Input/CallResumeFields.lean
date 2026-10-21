import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack PanSemStateFiniteExact

theorem continuation_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (value : ValueHOL 64) :
    LocalEffects.erase (continuationEntry source target name value)=LocalEffects.erase target := rfl

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.continuation_erase
