import InitECandidate.Solver.Input.VarList.RecordCells

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

/-- Actual decoded counts share the finite copied-input budget, including
empty arrays; no ordinary-domain or hypothetical parser-validity premise. -/
theorem Records.count_input_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (records : Records source input pointer array start length) :
    decodedCount input start length≤(input.length%2^64)/4 := by
  rcases records with empty | ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩
  · simp [decodedCount,empty]
  · have header := plan.header
    have slice := plan.slice
    have positive := plan.positive
    rw [lengthEq] at header
    rw [startEq,lengthEq] at slice
    have nonempty : length≠0 := by omega
    simp only [decodedCount,if_neg nonempty]
    rw [countEq] at header
    omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.count_input_bound
