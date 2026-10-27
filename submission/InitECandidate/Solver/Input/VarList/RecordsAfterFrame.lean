import InitECandidate.Solver.Input.VarList.RecordsFrame
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

/-- Actual decoded record arrays survive writes confined before their real
allocation boundary. Empty arrays impose no readable-pointer requirement. -/
theorem Records.of_after (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length boundary : Nat) (records : Records source input pointer array start length)
    (after : boundary≤array.toNat) (frame : ∀ query,boundary≤query.toNat → target.memory query=source.memory query) :
    Records target input pointer array start length := by
  classical
  by_cases empty : length=0
  · exact Or.inl empty
  have nonempty := records
  rcases nonempty with impossible | ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩
  · exact False.elim (empty impossible)
  have countValue : decodedCount input start length=plan.count := by simp only [decodedCount,if_neg empty]; exact countEq.symm
  apply Records.of_cells source target input pointer array start length records
  intro index inside
  have planInside : index<plan.count := by rw [← countValue]; exact inside
  simp only [decodedArray,if_neg empty,← arrayEq]
  constructor
  · apply frame
    rw [plan.row_nat index planInside,arrayEq]
    omega
  · apply frame
    rw [plan.length_nat index planInside,arrayEq]
    omega

/-- A single earlier scalar store preserves every initialized record cell. -/
theorem Records.store_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array destination word : BitVec 64) (start length : Nat)
    (records : Records source input pointer array start length) (before : destination.toNat < array.toNat) :
    Records {source with memory := WitnessRadix.StoreWord.put source.memory destination word}
      input pointer array start length := by
  apply Records.of_after source _ input pointer array start length array.toNat records (Nat.le_refl _)
  intro query after
  have away : query ≠ destination := by intro same; rw [same] at after; omega
  simp [WitnessRadix.StoreWord.put, away]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.of_after

#print axioms InitECandidate.Solver.Input.VarList.Records.store_before
