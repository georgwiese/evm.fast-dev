import InitECandidate.Solver.Mpt.WitnessDecodeMemory

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Parent-encoding metadata overwrites only8/16. Every other actual
constructor field, including path/value words, survives in the real leaf. -/
theorem leaf_constructor_cells_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words parentWords : String→BitVec 64)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {leafAllocated source heap words with memory:=WordWrites.write (leafAllocated source heap words).memory (LocalFields.writes heap (leafFields parentWords))}) :
    ∀ field∈NodeConstructor.fields .leaf words,field.offset≠8→field.offset≠16→
      target.memory (heap+BitVec.ofNat 64 field.offset)=.word field.value.word := by
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (leafAllocated source heap words).memory (LocalFields.writes heap (leafFields parentWords)) at memory
  intro field member notEight notSixteen
  have away : heap+BitVec.ofNat 64 field.offset∉(LocalFields.writes heap (leafFields parentWords)).map Prod.fst:=by
    simp only [NodeConstructor.fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp_all [LocalFields.writes,leafFields,BitVec.add_right_inj]
  rw [memory,WordWrites.write_away _ _ _ away]
  exact WordWrites.write_unique source.memory (FieldStores.writes heap (NodeConstructor.fields .leaf words))
    (heap+BitVec.ofNat 64 field.offset,field.value.word) (NodeConstructor.fields_distinct .leaf words heap) (List.mem_map.mpr ⟨field,member,rfl⟩)

theorem leaf_parent_cells_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words parentWords : String→BitVec 64)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {leafAllocated source heap words with memory:=WordWrites.write (leafAllocated source heap words).memory (LocalFields.writes heap (leafFields parentWords))}) :
    ∀ field∈leafFields parentWords,target.memory (heap+BitVec.ofNat 64 field.offset)=.word field.value.word := by
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (leafAllocated source heap words).memory (LocalFields.writes heap (leafFields parentWords)) at memory
  have distinct : ((LocalFields.writes heap (leafFields parentWords)).map Prod.fst).Nodup:=by
    simp [LocalFields.writes,leafFields,BitVec.add_right_inj]
  intro field member
  rw [memory]
  exact WordWrites.write_unique _ _ (heap+BitVec.ofNat 64 field.offset,field.value.word) distinct (List.mem_map.mpr ⟨field,member,rfl⟩)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_constructor_cells_of_post
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_parent_cells_of_post
