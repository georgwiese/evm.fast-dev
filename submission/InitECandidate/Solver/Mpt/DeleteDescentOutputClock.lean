import InitECandidate.Solver.Mpt.DeleteDescentOutputPure

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact

/-- Reattach the caller clock preceding a genuine paid pure prefix.
Every descent frame and progress fact uses the same physical state. -/
theorem DescentOutput.of_clock (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (clock : Nat)
    (output : DescentOutput {source with clock:=clock} target key length limit nodeLower pathLower property
      (model.with_clock source key length limit nodeLower pathLower property clock)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) :=
  ⟨{output with next:=output.next}⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.DescentOutput.of_clock
