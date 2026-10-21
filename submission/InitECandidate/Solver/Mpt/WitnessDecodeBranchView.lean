import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.Mpt.WitnessDecodeMemory

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchDescription (array pointer length listPointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (node : BitVec 64) : WitnessRecord.Description:=
  ⟨array,pointer,length,listPointer,bytes,items,.branch node 0 0⟩

/-- The real original branch return establishes a complete physical record
view, initialized counters and owned branch node, with its current heap and
scratch. All region and progress facts are derived from actual allocations. -/
theorem branch_view_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db array pointer length count listPointer heap cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (countExact : count.toNat=items.length)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (arrayFloor : 2713731432≤array.toNat) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (parentBound : length.toNat≤1024) (parentLower : 2713731432≤pointer.toNat)
    (parentBeforeDb : pointer.toNat+length.toNat≤db.toNat)
    (payloadLower : pointer.toNat≤listPointer.toNat) (payloadUpper : listPointer.toNat+bytes≤pointer.toNat+length.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source branchBody=(some (.returned value),target)) :
    let data:=branchDescription array pointer length listPointer bytes items heap
    let next:=PersistentAlloc.rounded heap 176#64
    value=.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))] ∧
      WitnessRecord.View target (WitnessRecord.pointer cursor) db data ∧ data.BeforeHeap next.toNat ∧
      Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧ AllocatedBytes.Arena next 0 ∧ next.toNat%8=0 ∧
      heap.toNat+176≤next.toNat ∧
      ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88 := by
  let words:=branchWords array pointer length heap
  let data:=branchDescription array pointer length listPointer bytes items heap
  let next:=PersistentAlloc.rounded heap 176#64
  obtain ⟨countEq,nodeArena,room,recordArena,nextScratch,decreases,valueEq,funded,post⟩:=
    branch_normal source target array pointer length count heap cursor limit arrayCell pointerCell lengthCell sliceCell heapCell heapArena heapAligned arena installed value normal
  obtain ⟨buffer,recordLower,recordUpper,recordAligned,recordNonzero⟩:=WitnessRecord.allocation_bounds source cursor limit arena room
  have scratchBelowHeap : cursor.toNat≤heap.toNat:=by omega
  have domain:=congrArg PanSemStateFiniteExact.memaddrs post
  change target.memaddrs=source.memaddrs at domain
  have currentRows : Rows target array listPointer bytes items:=by
    apply rows.frame source target array listPointer bytes items domain
    intro query lower upper
    exact branch_memory_of_post source target heap cursor limit words arena room nodeArena post query (by omega) (Or.inl (by omega))
  have tag:=branch_tag_of_post source target heap cursor limit words arena room scratchBelowHeap post
  have cellsEq : data.cells=(branchFields words).map (fun field=>(field.offset,field.value.word)):=by
    simp [data,branchDescription,WitnessRecord.Description.cells,words,branchFields,branchWords,LocalFields.Operand.word]
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words)) at memory
  have actualCells : ∀ entry∈data.cells,target.memory (WitnessRecord.pointer cursor+BitVec.ofNat 64 entry.1)=.word entry.2:=by
    intro entry member
    rw [cellsEq] at member
    obtain ⟨field,inFields,same⟩:=List.mem_map.mp member
    subst entry
    rw [memory]
    exact WordWrites.write_unique (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words))
      (WitnessRecord.pointer cursor+BitVec.ofNat 64 field.offset,field.value.word) (RecordKind.fields_distinct .branch words _) (List.mem_map.mpr ⟨field,inFields,rfl⟩)
  have countLength : items.length=17:=by rw [←countExact,countEq]; rfl
  have view : WitnessRecord.View target (WitnessRecord.pointer cursor) db data:=
    ⟨recordArena,recordAligned,by omega,arrayFloor,by change 2713731432≤heap.toNat; omega,actualCells,currentRows,countLength,
      parentBound,parentLower,parentBeforeDb,payloadLower,payloadUpper,nodeArena,heapAligned,tag⟩
  have checked:=PersistentAlloc.guards heap 176#64 nodeArena.upper
  have grows : heap.toNat+176≤next.toNat:=checked.2.2.1
  have nextArena : AllocatedBytes.Arena next 0:=⟨by have lower:=heapArena.lower; omega,by have upper:=checked.2.2.2.1; omega⟩
  have beforeNext : data.BeforeHeap next.toNat:=⟨beforeArray.trans (by omega),grows⟩
  have globals:=congrArg PanSemStateFiniteExact.globals post
  change target.globals=(Arenas.post (PersistentAlloc.post source heap 176#64) .down cursor 88#64).globals at globals
  have nextHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)):=by
    rw [globals]
    simp [Arenas.post,Arenas.pointerName,PersistentAlloc.post,next,HolFiniteMapExact.update,FUPDATE,
      show ofString "scratch_ptr"≠ofString "heap_ptr" from by decide]
  exact ⟨valueEq,view,beforeNext,nextScratch,nextHeap,nextArena,checked.2.2.2.2,grows,decreases⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_view_normal
