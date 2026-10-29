import InitECandidate.Solver.Mpt.NodeConstructorNormal

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def tag : Kind→BitVec 64 | .hashed=>0#64 | .leaf=>1#64 | .extension=>2#64 | .branch=>3#64

/-- The fixed constructor offsets remain distinct under the real word
address addition, including its original wrapping semantics. -/
theorem fields_distinct (kind : Kind) (words : String→BitVec 64) (heap : BitVec 64) :
    ((FieldStores.writes heap (fields kind words)).map Prod.fst).Nodup := by
  have offsets : ((fields kind words).map (fun field=>BitVec.ofNat 64 field.offset)).Nodup:=by
    cases kind <;> simp only [fields,List.map_cons,List.map_nil] <;> decide
  have injective : Function.Injective (fun offset : BitVec 64=>heap+offset):=by
    intro first second same
    exact (BitVec.add_right_inj heap).1 same
  have shifted:=List.Pairwise.map (S := fun first second : BitVec 64=>first≠second) (fun offset : BitVec 64=>heap+offset)
    (fun first second different equal=>different (injective equal)) offsets
  simpa only [List.Nodup,FieldStores.writes,List.map_map,Function.comp_def] using shifted

/-- Every actual scalar field, including constructor tags and saved ABI
words, follows from the real last-write memory effect of normal execution. -/
theorem scalar_normal_cells (kind : Kind) (scalar : kind≠.branch)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String→BitVec 64)
    (inputs : Inputs kind source words) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),target)) :
    ∀ field∈fields kind words,target.memory (heap+BitVec.ofNat 64 field.offset)=.word field.value.word := by
  obtain ⟨valueEq,nodeArena,positive,frame⟩:=scalar_normal_from_arena kind scalar source target heap words inputs domain heapCell arena aligned installed value normal
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  change target.memory=WordWrites.write source.memory (FieldStores.writes heap (fields kind words)) at memory
  intro field inside
  rw [memory]
  exact WordWrites.write_unique source.memory (FieldStores.writes heap (fields kind words)) (heap+BitVec.ofNat 64 field.offset,field.value.word)
    (fields_distinct kind words heap) (List.mem_map.mpr ⟨field,inside,rfl⟩)

theorem scalar_normal_tag (kind : Kind) (scalar : kind≠.branch)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String→BitVec 64)
    (inputs : Inputs kind source words) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),target)) : target.memory heap=.word (tag kind) := by
  have head : (⟨0,.literal (tag kind)⟩ : FieldStores.Field)∈fields kind words:=by
    cases kind <;> try exact (scalar rfl).elim
    all_goals simp [fields,tag]
  simpa only [FieldStores.Value.word,BitVec.add_zero] using
    scalar_normal_cells kind scalar source target heap words inputs domain heapCell arena aligned installed value normal _ head

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.fields_distinct
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_normal_cells
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_normal_tag
