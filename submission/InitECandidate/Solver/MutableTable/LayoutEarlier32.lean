import InitECandidate.Solver.MutableTable.LayoutSetCall32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack WitnessRadix

theorem earlier_ne (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (query : BitVec 64)
    (earlier : query.toNat<plan.table) (pool : Pool) (offset : Nat) (inside : offset<size plan pool) :
    query≠cell plan pool offset := by
  intro same
  have numbers:=congrArg BitVec.toNat same
  rw [number plan ready pool offset inside] at numbers
  have low:=(bounds plan ready pool).1
  omega

/-- Full insertion leaves all earlier input, slice records, scratch buffers
and gas/state cells unchanged whenever they lie below the private table. -/
theorem result_earlier (memory : WordWrites.Memory) (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (key : BitVec 64) (index count : Nat) (indexInside : index<plan.capacity) (countInside : count<plan.capacity)
    (value query : BitVec 64) (words : Fin 4→BitVec 64) (earlier : query.toNat<plan.table) :
    resultMemory memory plan key index count value words query=memory query := by
  apply Insert.result_away
  · rw [copy_addresses]
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨earlier_ne plan ready query earlier .keys _ (by change _<32*plan.capacity;omega),
      earlier_ne plan ready query earlier .keys _ (by change _<32*plan.capacity;omega),
      earlier_ne plan ready query earlier .keys _ (by change _<32*plan.capacity;omega),
      earlier_ne plan ready query earlier .keys _ (by change _<32*plan.capacity;omega)⟩
  · rw [value_cell]
    exact earlier_ne plan ready query earlier .values _ (by change _<8*plan.capacity;omega)
  · rw [used_byte_cell plan ready key index indexInside]
    exact earlier_ne plan ready query earlier .used _ (by change _<plan.capacity;omega)
  · rw [metadata_addresses]
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨earlier_ne plan ready query earlier .order _ (by change _<8*plan.capacity;omega),
      earlier_ne plan ready query earlier .position _ (by change _<8*plan.capacity;omega),
      earlier_ne plan ready query earlier .header 24 (by change 24<72;decide)⟩

theorem update_earlier (memory : WordWrites.Memory) (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (index : Nat) (inside : index<plan.capacity) (value query : BitVec 64) (earlier : query.toNat<plan.table) :
    updateMemory memory plan index value query=memory query := by
  apply if_neg
  rw [value_cell]
  exact earlier_ne plan ready query earlier .values _ (by change _<8*plan.capacity;omega)

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.result_earlier
#print axioms InitECandidate.Solver.MutableTable.Layout32.update_earlier
