import InitECandidate.Solver.PanFieldStoresFrame

namespace InitECandidate.Solver.Mpt.BranchValueUpdate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def fields (pointerName sizeName : String) (pointer size : BitVec 64) : List FieldStores.Field:=
  [⟨160,.saved pointerName pointer⟩,⟨168,.saved sizeName size⟩]

def program (nodeName pointerName sizeName : String) (pointer size : BitVec 64) (continuation : ProgHOL 64) : ProgHOL 64:=
  FieldStores.program nodeName "" (fields pointerName sizeName pointer size) continuation

def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer size : BitVec 64):=
  {source with memory:=WordWrites.write source.memory (FieldStores.writes node (fields "vptr" "vlen" pointer size))}

/-- Execute the actual two branch-value stores with the caller's scalar
names, then continue at the exact original suffix. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer size : BitVec 64)
    (nodeName pointerName sizeName : String) (continuation : ProgHOL 64)
    (nodeCell : source.locals.lookup (ofString nodeName)=some (.val (.word node)))
    (pointerCell : source.locals.lookup (ofString pointerName)=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString sizeName)=some (.val (.word size)))
    (pointerMapped : source.memaddrs (node+160#64)) (sizeMapped : source.memaddrs (node+168#64)) :
    evaluateHOLFiniteState source (program nodeName pointerName sizeName pointer size continuation)=
      evaluateHOLFiniteState (post source node pointer size) continuation := by
  have ready (field : FieldStores.Field) (member : field∈fields pointerName sizeName pointer size) : field.value.Ready source "" 0#64:=by
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact pointerCell
    · exact sizeCell
  have mapped (field : FieldStores.Field) (member : field∈fields pointerName sizeName pointer size) : source.memaddrs (node+BitVec.ofNat 64 field.offset):=by
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact pointerMapped
    · exact sizeMapped
  have avoid (reader : FieldStores.Field) (member : reader∈fields pointerName sizeName pointer size)
      (writer : FieldStores.Field) (writerIn : writer∈fields pointerName sizeName pointer size) : reader.value.Avoid 0#64 (node+BitVec.ofNat 64 writer.offset):=by
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> trivial
  exact FieldStores.execute source nodeName "" node 0#64 (fields pointerName sizeName pointer size) nodeCell ready mapped avoid continuation

theorem post_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer size query : BitVec 64)
    (away160 : query≠node+160#64) (away168 : query≠node+168#64) :
    (post source node pointer size).memory query=source.memory query := by
  apply WordWrites.write_away
  simpa [FieldStores.writes,fields] using And.intro away160 away168

theorem post_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer size : BitVec 64) :
    (post source node pointer size).memory (node+160#64)=.word pointer ∧
      (post source node pointer size).memory (node+168#64)=.word size := by
  simp [post,fields,FieldStores.writes,WordWrites.write,StoreWord.put,FieldStores.Value.word,BitVec.add_right_inj]

end InitECandidate.Solver.Mpt.BranchValueUpdate

#print axioms InitECandidate.Solver.Mpt.BranchValueUpdate.execute
#print axioms InitECandidate.Solver.Mpt.BranchValueUpdate.post_away
#print axioms InitECandidate.Solver.Mpt.BranchValueUpdate.post_cells
