import InitECandidate.Solver.Rlp.SliceRecordAt
import InitECandidate.Solver.Rlp.ValidationWriteFrame

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack PanSemStateFiniteExact

theorem Records.above (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (items : List ListItem) (cutoff : Nat)
    (records : Records source.memory array pointer items) (frame : Validation.Above source target cutoff)
    (below : cutoff≤array.toNat) (fits : array.toNat+16*items.length<2^64) : Records target.memory array pointer items := by
  induction items generalizing array pointer with
  | nil => trivial
  | cons item items ih =>
    have lengthNumber : (array+8#64).toNat=array.toNat+8 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat+8<2^64; simp only [List.length_cons] at fits; omega)]
      rfl
    have nextNumber : (array+16#64).toNat=array.toNat+16 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat+16<2^64; simp only [List.length_cons] at fits; omega)]
      rfl
    refine ⟨(frame array below).trans records.1,(frame (array+8#64) (by rw [lengthNumber]; omega)).trans records.2.1,?_⟩
    exact ih (array+16#64) (pointer+item.total) records.2.2 (by rw [nextNumber]; omega)
      (by rw [nextNumber]; simp only [List.length_cons] at fits; omega)

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.Records.at
#print axioms InitECandidate.Solver.Rlp.Slices.Records.above
