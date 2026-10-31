import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.Mpt.WitnessDecodeExtensionNormal
import InitECandidate.Solver.Mpt.WitnessRecordMemory
import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def extensionDescription (array pointer length listPointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (nibbles nibbleLength : BitVec 64) : WitnessRecord.Description:=
  ⟨array,pointer,length,listPointer,bytes,items,.extension nibbles nibbleLength⟩

/-- A genuine original extension return establishes its physical record
view and bounded nonempty owned nibble buffer. Scratch room/progress and
every stored field follow from the actual guarded allocation and return. -/
theorem extension_view_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db array pointer length listPointer nibbles nibbleLength leaf heap cursor limit : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (count : items.length=2)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (nibbleArena : AllocatedBytes.Arena nibbles nibbleLength.toNat) (nibbleBound : nibbleLength.toNat≤2048)
    (nibbleBefore : nibbles.toNat+nibbleLength.toNat≤heap.toNat)
    (parentBound : length.toNat≤1024) (parentLower : 2701131776≤pointer.toNat)
    (parentBeforeDb : pointer.toNat+length.toNat≤db.toNat)
    (payloadLower : pointer.toNat≤listPointer.toNat) (payloadUpper : listPointer.toNat+bytes≤pointer.toNat+length.toNat)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source extensionBody=(some (.returned value),target)) :
    let data:=extensionDescription array pointer length listPointer bytes items nibbles nibbleLength
    value=.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))] ∧
      WitnessRecord.View target (WitnessRecord.pointer cursor) db data ∧ data.BeforeHeap heap.toNat ∧
      Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88 ∧
      LiveFrame source target heap cursor limit := by
  let words:=extensionWords array pointer length nibbles nibbleLength
  let data:=extensionDescription array pointer length listPointer bytes items nibbles nibbleLength
  obtain ⟨nonempty,room,recordArena,nextArena,recordUpper,decreases,valueEq,funded,post⟩:=extension_normal source target array pointer length nibbles nibbleLength leaf cursor limit
    arrayCell pointerCell lengthCell compactCell arena live.code value normal
  have positive : 0<nibbleLength.toNat:=by
    by_contra bad
    apply nonempty
    apply BitVec.eq_of_toNat_eq
    change nibbleLength.toNat=0
    omega
  obtain ⟨buffer,recordLower,recordBound,recordAligned,recordNonzero⟩:=WitnessRecord.allocation_bounds source cursor limit arena room
  obtain ⟨limitLower,cursorUpper⟩:=live.bounds arena
  have domain:=congrArg PanSemStateFiniteExact.memaddrs post
  change target.memaddrs=source.memaddrs at domain
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (extensionFields words)) at memory
  have currentRows : Rows target array listPointer bytes items:=by
    apply rows.frame source target array listPointer bytes items domain
    intro query lower upper
    rw [memory]
    exact WitnessRecord.writes_outside source cursor limit arena room (extensionFields words)
      (by intro field member; have bound:=extension_geometry words field member; omega) source.memory query (Or.inl (by omega))
  have cellsEq : data.cells=(extensionFields words).map (fun field=>(field.offset,field.value.word)):=by
    simp [data,extensionDescription,WitnessRecord.Description.cells,words,extensionFields,extensionWords,LocalFields.Operand.word]
  have actualCells : ∀ entry∈data.cells,target.memory (WitnessRecord.pointer cursor+BitVec.ofNat 64 entry.1)=.word entry.2:=by
    intro entry member
    rw [cellsEq] at member
    obtain ⟨field,inFields,same⟩:=List.mem_map.mp member
    subst entry
    rw [memory]
    exact WordWrites.write_unique source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (extensionFields words))
      (WitnessRecord.pointer cursor+BitVec.ofNat 64 field.offset,field.value.word) (RecordKind.fields_distinct .extension words _) (List.mem_map.mpr ⟨field,inFields,rfl⟩)
  have view : WitnessRecord.View target (WitnessRecord.pointer cursor) db data:=
    ⟨recordArena,recordAligned,by omega,rows.allocation.lower,nibbleArena.lower,actualCells,currentRows,count,parentBound,parentLower,parentBeforeDb,payloadLower,payloadUpper,
      ⟨positive,nibbleBound,nibbleArena⟩,trivial,by omega,
        ⟨beforeArray.trans heapBound,nibbleBefore.trans heapBound⟩⟩
  have before : data.BeforeHeap heap.toNat:=⟨beforeArray,nibbleBefore⟩
  have globals:=congrArg PanSemStateFiniteExact.globals post
  change target.globals=(Arenas.post source .down cursor 88#64).globals at globals
  have nextHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by
    rw [globals]
    simpa [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE,
      show ofString "scratch_ptr"≠ofString "heap_ptr" from by decide] using heapCell
  have codeEq:=congrArg PanSemStateFiniteExact.code post
  change target.code=source.code at codeEq
  have finalLive:=Rlp.LiveArena.of_validation nextArena limitLower (by omega) (by rw [codeEq]; exact live.code)
  have runtime:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>Input.MemoryMetadata.erase {state with globals:=source.globals}) post
  change Input.MemoryMetadata.erase {target with globals:=source.globals}=Input.MemoryMetadata.erase source at runtime
  have outside (query : BitVec 64) (location : query.toNat<limit.toNat ∨ cursor.toNat≤query.toNat) : target.memory query=source.memory query:=by
    rw [memory]
    exact WitnessRecord.writes_outside source cursor limit arena room (extensionFields words)
      (by intro field member; have bound:=extension_geometry words field member; omega) source.memory query location
  have frame : LiveFrame source target heap cursor limit:=
    ⟨⟨heap,nextHeap,heapArena,heapBound,heapAligned,Nat.le_refl _⟩,
      ⟨WitnessRecord.pointer cursor,nextArena,by omega⟩,finalLive,runtime,
      by
        intro key notHeap notScratch
        rw [globals]
        simp [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE,Ne.symm notScratch],
      fun query earlier=>outside query (Or.inl (by omega)),
      fun query above=>outside query (Or.inr above)⟩
  exact ⟨valueEq,view,before,nextArena,nextHeap,decreases,frame⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_view_normal
