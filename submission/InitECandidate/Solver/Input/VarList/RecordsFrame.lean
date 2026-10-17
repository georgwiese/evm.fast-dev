import InitECandidate.Solver.Input.VarList.RecordCells

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

/-- Decoded records depend only on their two actual cells per item; other
memory, code, clocks, locals and globals can change. -/
theorem Records.of_cells (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (records : Records source input pointer array start length)
    (same : ∀ index<decodedCount input start length,
      target.memory (row (decodedArray array length) index)=source.memory (row (decodedArray array length) index) ∧
      target.memory (lengthCell (decodedArray array length) index)=source.memory (lengthCell (decodedArray array length) index)) :
    Records target input pointer array start length := by
  classical
  rcases records with empty|nonempty
  · exact Or.inl empty
  · obtain ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩:=nonempty
    have ne : length≠0 := by have h:=plan.header;have p:=plan.positive;rw [lengthEq] at h;omega
    have countValue : decodedCount input start length=plan.count := by simp only [decodedCount,if_neg ne];exact countEq.symm
    refine Or.inr ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,?_,valid⟩
    intro index inside
    have memory:=same index (by rw [countValue];exact inside)
    simp only [decodedArray,if_neg ne,←arrayEq] at memory
    change _ ∧ _
    rw [memory.1,memory.2]
    exact complete index inside

/-- Earlier decoded arrays survive a later allocation whose execution preserves
all words before its boundary. This retains their original input-offset proof. -/
theorem Records.of_before (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length boundary : Nat) (records : Records source input pointer array start length)
    (before : array.toNat+16*decodedCount input start length≤boundary)
    (frame : ∀ query,query.toNat<boundary→target.memory query=source.memory query) :
    Records target input pointer array start length := by
  classical
  by_cases empty : length=0
  · exact Or.inl empty
  · have nonempty:=records
    rcases nonempty with impossible|⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩
    · exact False.elim (empty impossible)
    · have countValue : decodedCount input start length=plan.count := by simp only [decodedCount,if_neg empty];exact countEq.symm
      apply Records.of_cells source target input pointer array start length records
      intro index inside
      have planInside : index<plan.count := by rw [←countValue];exact inside
      simp only [decodedArray,if_neg empty,←arrayEq]
      constructor
      · apply frame
        rw [plan.row_nat index planInside]
        rw [arrayEq]
        omega
      · apply frame
        rw [plan.length_nat index planInside]
        rw [arrayEq]
        omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.of_cells
#print axioms InitECandidate.Solver.Input.VarList.Records.of_before
