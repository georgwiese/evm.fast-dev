import InitECandidate.Solver.Input.PayloadImage

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- The original fifteen later writes complete the full seventeen-word
payload image while retaining its two earlier physical header cells. -/
theorem image_after_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length array : BitVec 64) (room : cursor.toNat+136≤33806089496)
    (headerPointer : source.memory cursor=.word (pointer+62#64))
    (headerLength : source.memory (cursor+8#64)=.word length) :
    Image (applyFields source cursor (afterExtraFields input pointer length array)) input pointer cursor length array := by
  have valid (field : Field) (member : field∈afterExtraFields input pointer length array) : field.1≤128 :=
    (image_fields_valid input pointer length array field (by simp only [imageFields,List.mem_append]; exact Or.inr member)).1
  intro field member
  have bound := (image_fields_valid input pointer length array field member).1
  rw [applyFields_cell source cursor room (afterExtraFields input pointer length array) valid field.1 bound]
  simp only [imageFields,afterExtraFields,remainingFields,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [afterExtraFields,remainingFields,cellValue,headerPointer,headerLength]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.image_after_fields
