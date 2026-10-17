import InitECandidate.Solver.Input.VarList.RecordsFrame
import InitECandidate.Solver.WitnessRadix.AllocatedAway

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Actual decoded arrays survive constructor writes to fixed hash buffers and
a later private allocation. Empty arrays require no cells or positive pointer. -/
theorem Records.of_safe_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length table : Nat) (records : Records source input pointer array start length)
    (arrayBefore : array.toNat+16*decodedCount input start length≤table)
    (stp pad out : BitVec 64)
    (stateArena : AllocatedBytes.Arena stp 200) (paddingArena : AllocatedBytes.Arena pad 136) (outputArena : AllocatedBytes.Arena out 32)
    (buffersBefore : stp.toNat+200≤array.toNat ∧ pad.toNat+136≤array.toNat ∧ out.toNat+32≤array.toNat)
    (frame : ∀ query,query.toNat<table ∧ Keccak256.Protected stp pad out query → target.memory query=source.memory query) :
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
      have planInside : index<plan.count:=by rw [←countValue];exact inside
      have rowNumber:=plan.row_nat index planInside
      have lengthNumber:=plan.length_nat index planInside
      rw [arrayEq] at rowNumber lengthNumber
      have safe (query : BitVec 64) (lower : array.toNat≤query.toNat)
          (upper : query.toNat<array.toNat+16*decodedCount input start length) :
          target.memory query=source.memory query := by
        apply frame
        refine ⟨by omega,?_,?_,?_⟩
        · exact AllocatedBytes.Arena.away_above stp query 200 stateArena (by have:=buffersBefore.1;omega)
        · exact AllocatedBytes.Arena.away_above pad query 136 paddingArena (by have:=buffersBefore.2.1;omega)
        · exact AllocatedBytes.Arena.away_above out query 32 outputArena (by have:=buffersBefore.2.2;omega)
      simp only [decodedArray,if_neg empty,←arrayEq]
      constructor
      · exact safe _ (by rw [arrayEq,rowNumber];omega) (by rw [arrayEq,rowNumber];omega)
      · exact safe _ (by rw [arrayEq,lengthNumber];omega) (by rw [arrayEq,lengthNumber];omega)

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.of_safe_frame
