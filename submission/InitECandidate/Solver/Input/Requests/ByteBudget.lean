import InitECandidate.Solver.Input.Requests.ImageLayout

namespace InitECandidate.Solver.Input.Requests
open Flapjack PanSemStateFiniteExact

def boundary (words : Nat → BitVec 64) (total : BitVec 64) (index : Nat) := if index < 5 then (words index).toNat else total.toNat

theorem Layout.ordered (words : Nat → BitVec 64) (total : BitVec 64) (layout : Layout words total) (index : Nat) (small : index < 5) :
    boundary words total index ≤ boundary words total (index+1) := by
  by_cases more : index+1 < 5
  · have valid := layout.valid (index+1) more
    have order := valid.2.2 (by omega)
    simpa [boundary,small,more] using order
  · simpa [boundary,small,more] using (layout.valid index small).2.1

theorem Layout.span_number (words : Nat → BitVec 64) (total : BitVec 64) (layout : Layout words total) (index : Nat) (small : index < 5) :
    (countSpan words total index).toNat = boundary words total (index+1) - boundary words total index := by
  by_cases more : index+1 < 5
  · have valid := layout.valid (index+1) more
    have order : words index ≤ words (index+1) := by
      change (words index).toNat ≤ (words (index+1)).toNat
      simpa using valid.2.2 (by omega)
    simpa [countSpan,boundary,small,more] using BitVec.toNat_sub_of_le order
  · have order : words index ≤ total := (layout.valid index small).2.1
    simpa [countSpan,boundary,small,more] using BitVec.toNat_sub_of_le order

/-- The five actual request slices partition exactly the variable payload,
with their real20-byte fixed prefix counted once. -/
theorem Layout.byte_partition (words : Nat → BitVec 64) (total : BitVec 64) (layout : Layout words total) :
    (countSpan words total 0).toNat + (countSpan words total 1).toNat + (countSpan words total 2).toNat +
      (countSpan words total 3).toNat + (countSpan words total 4).toNat + 20 = total.toNat := by
  have o0 := Layout.ordered words total layout 0 (by decide)
  have o1 := Layout.ordered words total layout 1 (by decide)
  have o2 := Layout.ordered words total layout 2 (by decide)
  have o3 := Layout.ordered words total layout 3 (by decide)
  have o4 := Layout.ordered words total layout 4 (by decide)
  have s0 := Layout.span_number words total layout 0 (by decide)
  have s1 := Layout.span_number words total layout 1 (by decide)
  have s2 := Layout.span_number words total layout 2 (by decide)
  have s3 := Layout.span_number words total layout 3 (by decide)
  have s4 := Layout.span_number words total layout 4 (by decide)
  have first : (words 0).toNat = 20 := by rw [layout.first]; rfl
  simp [boundary] at o0 o1 o2 o3 o4 s0 s1 s2 s3 s4
  omega

theorem Image.element_bytes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer cursor total : BitVec 64) (words counts : Nat → BitVec 64)
    (image : Image source pointer cursor total words counts) (index : Nat) (small : index < 5) :
    (elementSize index).toNat * (counts index).toNat = (countSpan words total index).toNat := by
  obtain ⟨number,remainder⟩ := image.arithmetic index small
  have equation := Nat.mod_add_div (countSpan words total index).toNat (elementSize index).toNat
  rw [remainder,Nat.zero_add,←number] at equation
  exact equation

/-- Actual request records consume their original encoded sizes; summing
separate maximum counts for the five lists would overcount this shared input. -/
theorem Image.byte_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer cursor total : BitVec 64) (words counts : Nat → BitVec 64)
    (image : Image source pointer cursor total words counts) (layout : Layout words total) :
    192*(counts 0).toNat + 76*(counts 1).toNat + 116*(counts 2).toNat + 184*(counts 3).toNat + 68*(counts 4).toNat + 20 = total.toNat := by
  change (elementSize 0).toNat*(counts 0).toNat + (elementSize 1).toNat*(counts 1).toNat + (elementSize 2).toNat*(counts 2).toNat +
    (elementSize 3).toNat*(counts 3).toNat + (elementSize 4).toNat*(counts 4).toNat + 20 = _
  rw [Image.element_bytes source pointer cursor total words counts image 0 (by decide),Image.element_bytes source pointer cursor total words counts image 1 (by decide),
    Image.element_bytes source pointer cursor total words counts image 2 (by decide),Image.element_bytes source pointer cursor total words counts image 3 (by decide),
    Image.element_bytes source pointer cursor total words counts image 4 (by decide)]
  exact Layout.byte_partition words total layout

theorem Image.count_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer cursor total : BitVec 64) (words counts : Nat → BitVec 64)
    (image : Image source pointer cursor total words counts) (layout : Layout words total) :
    (counts 0).toNat + (counts 1).toNat + (counts 2).toNat + (counts 3).toNat + (counts 4).toNat ≤ (total.toNat - 20) / 68 := by
  have budget := Image.byte_budget source pointer cursor total words counts image layout
  omega

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.Layout.ordered
#print axioms InitECandidate.Solver.Input.Requests.Layout.span_number
#print axioms InitECandidate.Solver.Input.Requests.Layout.byte_partition
#print axioms InitECandidate.Solver.Input.Requests.Image.element_bytes
#print axioms InitECandidate.Solver.Input.Requests.Image.byte_budget
#print axioms InitECandidate.Solver.Input.Requests.Image.count_budget
