import InitECandidate.Solver.Input.VarList.RecordsFrame

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

/-- A prior decoded array survives writes below its base and fresh allocations
above its end. The frame is needed only on the array's actual interval. -/
theorem Records.of_interval (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length boundary : Nat) (records : Records source input pointer array start length)
    (before : array.toNat+16*decodedCount input start length≤boundary)
    (frame : ∀ query,array.toNat≤query.toNat → query.toNat<boundary → target.memory query=source.memory query) :
    Records target input pointer array start length := by
  classical
  by_cases empty : length=0
  · exact Or.inl empty
  · rcases records with impossible|⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩
    · exact False.elim (empty impossible)
    · have records : Records source input pointer array start length:=Or.inr ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩
      have countValue : decodedCount input start length=plan.count := by simp only [decodedCount,if_neg empty];exact countEq.symm
      apply Records.of_cells source target input pointer array start length records
      intro index inside
      have planInside : index<plan.count := by rw [←countValue];exact inside
      have rowNumber:=plan.row_nat index planInside
      have lengthNumber:=plan.length_nat index planInside
      rw [arrayEq] at rowNumber lengthNumber
      simp only [decodedArray,if_neg empty]
      exact ⟨frame _ (by rw [rowNumber];omega) (by rw [rowNumber];omega),
        frame _ (by rw [lengthNumber];omega) (by rw [lengthNumber];omega)⟩

/-- The two witness dictionaries share one byte budget. Counts derive from
actual decoded records on validated adjacent subranges of the encoded extent. -/
theorem witness_count_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer nodeArray codeArray : BitVec 64) (start first middle last total : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (ordered : first≤middle ∧ middle≤last ∧ last≤total) (inside : start+total≤input.length%2^64)
    (nodes : Records source input pointer nodeArray (start+first) (middle-first))
    (codes : Records source input pointer codeArray (start+middle) (last-middle)) :
    decodedCount input (start+first) (middle-first)+decodedCount input (start+middle) (last-middle)≤(input.length%2^64)/4 := by
  have leftBound:=(Records.cells source input pointer nodeArray (start+first) (middle-first) domain nodes).1
  have rightBound:=(Records.cells source input pointer codeArray (start+middle) (last-middle) domain codes).1
  omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.of_interval
#print axioms InitECandidate.Solver.Input.VarList.witness_count_bound
