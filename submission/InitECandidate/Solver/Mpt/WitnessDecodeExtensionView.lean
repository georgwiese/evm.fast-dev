import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.Mpt.WitnessDecodeExtensionNormal
import InitECandidate.Solver.Mpt.WitnessRecordMemory

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
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (arrayFloor : 2713731432≤array.toNat) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (nibbleArena : AllocatedBytes.Arena nibbles nibbleLength.toNat) (nibbleBound : nibbleLength.toNat≤2048)
    (nibbleFloor : 2713731432≤nibbles.toNat) (nibbleBefore : nibbles.toNat+nibbleLength.toNat≤heap.toNat)
    (parentBound : length.toNat≤1024) (parentLower : 2713731432≤pointer.toNat)
    (parentBeforeDb : pointer.toNat+length.toNat≤db.toNat)
    (payloadLower : pointer.toNat≤listPointer.toNat) (payloadUpper : listPointer.toNat+bytes≤pointer.toNat+length.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source extensionBody=(some (.returned value),target)) :
    let data:=extensionDescription array pointer length listPointer bytes items nibbles nibbleLength
    value=.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))] ∧
      WitnessRecord.View target (WitnessRecord.pointer cursor) db data ∧ data.BeforeHeap heap.toNat ∧
      Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88 := by
  let words:=extensionWords array pointer length nibbles nibbleLength
  let data:=extensionDescription array pointer length listPointer bytes items nibbles nibbleLength
  obtain ⟨nonempty,room,recordArena,nextArena,recordUpper,decreases,valueEq,funded,post⟩:=extension_normal source target array pointer length nibbles nibbleLength leaf cursor limit
    arrayCell pointerCell lengthCell compactCell arena installed value normal
  have positive : 0<nibbleLength.toNat:=by
    by_contra bad
    apply nonempty
    apply BitVec.eq_of_toNat_eq
    change nibbleLength.toNat=0
    omega
  obtain ⟨buffer,recordLower,recordBound,recordAligned,recordNonzero⟩:=WitnessRecord.allocation_bounds source cursor limit arena room
  have domain:=congrArg PanSemStateFiniteExact.memaddrs post
  change target.memaddrs=source.memaddrs at domain
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (extensionFields words)) at memory
  have currentRows : Rows target array listPointer bytes items:=by
    apply rows.frame source target array listPointer bytes items domain
    intro query lower upper
    rw [memory]
    exact WitnessRecord.writes_above source cursor limit arena room (extensionFields words)
      (by intro field member; have bound:=extension_geometry words field member; omega) source.memory query (by omega)
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
    ⟨recordArena,recordAligned,by omega,arrayFloor,nibbleFloor,actualCells,currentRows,count,parentBound,parentLower,parentBeforeDb,payloadLower,payloadUpper,
      positive,nibbleBound,nibbleArena⟩
  have before : data.BeforeHeap heap.toNat:=⟨beforeArray,nibbleBefore⟩
  have globals:=congrArg PanSemStateFiniteExact.globals post
  change target.globals=(Arenas.post source .down cursor 88#64).globals at globals
  have nextHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by
    rw [globals]
    simpa [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE,
      show ofString "scratch_ptr"≠ofString "heap_ptr" from by decide] using heapCell
  exact ⟨valueEq,view,before,nextArena,nextHeap,decreases⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_view_normal
