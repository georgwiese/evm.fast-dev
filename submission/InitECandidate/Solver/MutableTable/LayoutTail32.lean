import InitECandidate.Solver.MutableTable.LayoutHeader32
import InitECandidate.Solver.WitnessRadix.Copy32Alignment

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem source_copy_separate (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (key : BitVec 64)
    (index : Nat) (inside : index<plan.capacity) (before : key.toNat+32≤plan.table) (read write : Fin 4) :
    key+BitVec.ofNat 64 (8*read.val)≠
      (parameters plan key).keys+BitVec.ofNat 64 index*(parameters plan key).stride+BitVec.ofNat 64 (8*write.val) := by
  have fits:=ready.fits
  have first:=MemoryBytes.offset_toNat key (8*read.val) (by have:=read.isLt;omega)
  have second:=number plan ready .keys (32*index+8*write.val) (by change _<32*plan.capacity;have:=write.isLt;omega)
  rw [key_cell]
  intro equal
  have numbers:=congrArg BitVec.toNat equal
  rw [first,second] at numbers
  simp only [base] at numbers
  have:=read.isLt
  omega

/-- The complete actual insertion tail from a concrete original-table
header/layout and a separate aligned digest buffer. No store/copy run or
physical separation of table arrays is supplied as a premise. -/
theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (key : BitVec 64) (index count : Nat) (indexInside : index<plan.capacity) (countInside : count<plan.capacity)
    (value : BitVec 64) (words : Fin 4→BitVec 64) (header : Header source plan key count)
    (locals : Find.Locals source (parameters plan key) (BitVec.ofNat 64 index))
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (orderLocal : source.locals.lookup (ofString "order")=some (.val (.word (BitVec.ofNat 64 (base plan .order)))))
    (positionLocal : source.locals.lookup (ofString "order_pos")=some (.val (.word (BitVec.ofNat 64 (base plan .position)))))
    (aligned : key.toNat%8=0) (before : key.toNat+32≤plan.table) (little : source.be=false)
    (view : MemoryBytes.WordView source key words)
    (code : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one)) (enough : 2≤source.clock) :
    ∃ target,evaluateHOLFiniteState source Insert.afterLoop=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {source with memory:=resultMemory source.memory plan key index count value words,clock:=source.clock-2} := by
  have headerMapped (offset : Nat) (inside : offset<72) (aligned : offset%8=0) :
      source.memaddrs (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset) := by
    rw [header_cell plan offset]
    exact word_mapped source plan ready domain .header offset inside aligned
  apply Insert.tail32_execute source (parameters plan key) (BitVec.ofNat 64 plan.table)
    (BitVec.ofNat 64 (base plan .values)) (BitVec.ofNat 64 (base plan .order)) (BitVec.ofNat 64 (base plan .position))
    (BitVec.ofNat 64 index) (BitVec.ofNat 64 count) value locals rfl words tLocal valueLocal orderLocal positionLocal
    (headerMapped 40 (by decide) (by decide)) header.values
  · rw [value_cell]
    exact word_mapped source plan ready domain .values _ (by change _<8*plan.capacity;omega) (by omega)
  · exact used_mapped source plan ready domain key index indexInside
  · have address:=scaled_cell plan .order 8 count 0
    simp only [BitVec.add_zero,Nat.add_zero] at address
    rw [address]
    exact word_mapped source plan ready domain .order _ (by change _<8*plan.capacity;omega) (by omega)
  · have address:=scaled_cell plan .position 8 index 0
    simp only [BitVec.add_zero,Nat.add_zero] at address
    rw [address]
    exact word_mapped source plan ready domain .position _ (by change _<8*plan.capacity;omega) (by omega)
  · exact headerMapped 24 (by decide) (by decide)
  · exact header.count
  · rw [header_cell plan 24,value_cell]
    exact separate plan ready .header .values (by decide) _ _ (by change 24<72;decide) (by change _<8*plan.capacity;omega)
  · rw [header_cell plan 24,used_byte_cell plan ready key index indexInside]
    exact separate plan ready .header .used (by decide) _ _ (by change 24<72;decide) (by change _<plan.capacity;omega)
  · rw [header_cell plan 40]
    exact copy_away plan ready key index indexInside words .header 40 (by change 40<72;decide) (by decide)
  · rw [header_cell plan 24]
    exact copy_away plan ready key index indexInside words .header 24 (by change 24<72;decide) (by decide)
  · exact little
  · exact code
  · exact Copy32.alignment_mask key _ aligned (key_aligned plan ready key index indexInside)
  · exact view
  · exact key_mapped source plan ready domain key index indexInside
  · exact source_copy_separate plan ready key index indexInside before
  · exact enough

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.source_copy_separate
#print axioms InitECandidate.Solver.MutableTable.Layout32.tail_execute
