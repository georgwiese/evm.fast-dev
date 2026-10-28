import InitECandidate.Solver.Rlp.SliceRecordAt

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack PanSemStateFiniteExact

/-- Transport the actual record array through agreement on its own physical
word interval, independently of unrelated heap or scratch contents. -/
theorem Records.of_interval (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (items : List ListItem)
    (records : Records source.memory array pointer items) (fits : array.toNat+16*items.length<2^64)
    (frame : ∀ query : BitVec 64,array.toNat≤query.toNat → query.toNat<array.toNat+16*items.length → target.memory query=source.memory query) :
    Records target.memory array pointer items := by
  induction items generalizing array pointer with
  | nil=>trivial
  | cons item items ih=>
    have n8 : (array+8#64).toNat=array.toNat+8 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat+8<2^64; simp only [List.length_cons] at fits; omega)]; rfl
    have n16 : (array+16#64).toNat=array.toNat+16 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat+16<2^64; simp only [List.length_cons] at fits; omega)]; rfl
    refine ⟨(frame array (Nat.le_refl _) (by simp only [List.length_cons]; omega)).trans records.1,
      (frame (array+8#64) (by rw [n8]; omega) (by rw [n8]; simp only [List.length_cons]; omega)).trans records.2.1,?_⟩
    apply ih (array+16#64) (pointer+item.total) records.2.2
    · rw [n16]
      simp only [List.length_cons] at fits
      omega
    · intro query lower upper
      apply frame query
      · rw [n16] at lower
        omega
      · rw [n16] at upper
        simp only [List.length_cons]
        omega

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.Records.of_interval
