import InitECandidate.Solver.Mpt.WitnessCoreMetadata
import InitECandidate.Solver.Mpt.WitnessRecordIntervalFrame
import InitECandidate.Solver.Mpt.NodeConstructorNormal
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def extensionWords (nibbles length child : BitVec 64) : String→BitVec 64:=
  fun name=>if name="nib" then nibbles else if name="nlen" then length else child

def extensionAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nibbles length child : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  {PersistentAlloc.post {source with clock:=source.clock-2} heap 56#64 with
    memory:=WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .extension (extensionWords nibbles length child)))}

/-- A genuine continuing original extension constructor call derives
its own fresh56-byte allocation, performs the actual parent metadata and
pop, and restores ex. Allocation room and the two real caller ticks follow
from execution, rather than being required at entry. -/
theorem extension_create_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db heap nibbles length child previous : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.extension nibbles length)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (previousCell : source.memory record=.word previous)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (before : data.BeforeHeap heap.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source extensionCreate=(none,post)) :
    heap.toNat+56≤2952790016 ∧ AllocatedBytes.Arena heap 56 ∧ 2≤source.clock ∧
      post=restore source "ex" (metadataState (QueryBranch.bind (extensionAllocated source heap nibbles length child) "ex" heap)
        heap data.pointer data.length previous) := by
  have mapped64 : source.memaddrs (record+64#64):=by simpa only [byteAddress] using view.mapped source record db data 64 (by decide) (by decide)
  have mapped72 : source.memaddrs (record+72#64):=by simpa only [byteAddress] using view.mapped source record db data 72 (by decide) (by decide)
  have nibblesCell : source.memory (record+64#64)=.word nibbles:=view.cells (64,nibbles) (by simp [WitnessRecord.Description.cells,payload])
  have lengthCell : source.memory (record+72#64)=.word length:=view.cells (72,length) (by simp [WitnessRecord.Description.cells,payload])
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) extensionArguments=
      some [.val (.word nibbles),.val (.word length),.val (.word child)]:=by
    simp [extensionArguments,readAt,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,topCell,resultCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped64,mapped72,nibblesCell,lengthCell]
  obtain ⟨callee,called,nibblesLocal,lengthLocal,childLocal⟩:=Input.word_triple_environment source.code.lookup
    (ofString "node_new_ext") (ofString "nib") (ofString "nlen") (ofString "child") (NodeConstructor.body .extension) .one
    nibbles length child (by decide) (by decide) (by decide) (NodeConstructor.original_code .extension source.code installed)
  rw [extension_create_shape] at normal
  obtain ⟨funded,built,returned,inner,bodyRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none source post "ex" .one
    (ofString "node_new_ext") extensionArguments _ (NodeConstructor.body .extension) afterExtensionCreate callee .one args called normal
  have inputs : NodeConstructor.Inputs .extension (callEntryStateHOLFinite source callee) (extensionWords nibbles length child):=by
    simpa only [NodeConstructor.Inputs,callEntryStateHOLFinite,extensionWords,↓reduceIte,show ¬("child"="nib") from by decide,show ¬("child"="nlen") from by decide,
      show ¬("nlen"="nib") from by decide] using And.intro nibblesLocal (And.intro lengthLocal childLocal)
  have room : heap.toNat+56≤2952790016:=NodeConstructor.room_of_normal .extension
    (callEntryStateHOLFinite source callee) built heap heapCell heapArena installed returned bodyRun
  obtain ⟨returnedEq,checkedRoom,nodeArena,nodeFunding,nodeFrame⟩:=NodeConstructor.scalar_normal .extension (by decide)
    (callEntryStateHOLFinite source callee) built heap (extensionWords nibbles length child) inputs view.rows.domain heapCell heapArena (by omega) heapAligned installed returned bodyRun
  have memoryFrame:=NodeConstructor.scalar_normal_frame .extension (by decide)
    (callEntryStateHOLFinite source callee) built heap (extensionWords nibbles length child) inputs view.rows.domain heapCell heapArena (by omega) heapAligned installed returned bodyRun
  rw [returnedEq] at continued
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) nodeFrame
  change {built with locals:=source.locals}=
    {PersistentAlloc.post {source with clock:=source.clock-1-1} heap 56#64 with
      memory:=WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .extension (extensionWords nibbles length child)))} at callerFrame
  rw [Nat.sub_sub] at callerFrame
  change {built with locals:=source.locals}=extensionAllocated source heap nibbles length child at callerFrame
  let ready:=QueryBranch.bind (extensionAllocated source heap nibbles length child) "ex" heap
  change evaluateHOLFiniteState (QueryBranch.bind {built with locals:=source.locals} "ex" heap) afterExtensionCreate=(none,inner) at continued
  rw [callerFrame] at continued
  have memoryEq:=congrArg PanSemStateFiniteExact.memory callerFrame
  change built.memory=(extensionAllocated source heap nibbles length child).memory at memoryEq
  have oldMemory (query : BitVec 64) (upper : query.toNat<heap.toNat) : ready.memory query=source.memory query:=by
    change (extensionAllocated source heap nibbles length child).memory query=source.memory query
    rw [←memoryEq]
    exact memoryFrame query (Or.inl upper)
  have recordUpper:=view.ceiling
  have aboveMemory (query : BitVec 64) (above : record.toNat≤query.toNat) : ready.memory query=source.memory query:=by
    change (extensionAllocated source heap nibbles length child).memory query=source.memory query
    rw [←memoryEq]
    exact memoryFrame query (Or.inr (by have lower:=view.scratchLower; omega))
  have readyView:=view.regions_frame source ready record db heap.toNat record.toNat data before (Nat.le_refl _) rfl oldMemory aboveMemory
  have readyPrevious : ready.memory record=.word previous:=(aboveMemory record (Nat.le_refl _)).trans previousCell
  have readyTop : ready.locals.lookup (ofString "top")=some (.val (.word record)):=
    (bind_lookup_other _ "ex" "top" heap (by decide)).trans topCell
  have readyResult : ready.locals.lookup (ofString "result")=some (.val (.word child)):=
    (bind_lookup_other _ "ex" "result" heap (by decide)).trans resultCell
  have metadataRun:=parent_metadata_execute ready record db heap previous child data 56 "ex" readyView nodeArena (by decide)
    heapAligned room (by decide) readyTop (bind_lookup_same _ _ _) readyResult readyPrevious
  rw [after_extension_create_shape,metadataRun] at continued
  have innerEq : inner=metadataState ready heap data.pointer data.length previous:=(congrArg Prod.snd continued).symm
  refine ⟨room,nodeArena,?_,?_⟩
  · change 1≤source.clock-1 at nodeFunding
    omega
  · rw [endpoint,innerEq]

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_create_normal
