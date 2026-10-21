import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def metadataState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer length previous : BitVec 64) :=
  QueryBranch.bind (QueryBranch.bind {source with memory:=StoreWord.put (StoreWord.put source.memory (node+8#64) pointer) (node+16#64) length}
    "top" previous) "result" node

/-- Both original parent stores read the current physical record, then
the actual PREV word restores top and the new node becomes result. The
record's parent words need not equal the original function's p/n locals. -/
theorem parent_metadata_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node previous oldResult : BitVec 64) (data : WitnessRecord.Description) (size : Nat) (name : String)
    (view : WitnessRecord.View source record db data) (nodeArena : AllocatedBytes.Arena node size)
    (nodeSize : 24≤size) (nodeAligned : node.toNat%8=0) (nodeLower : 2713731432≤node.toNat)
    (different : ofString "top"≠ofString name)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (nodeCell : source.locals.lookup (ofString name)=some (.val (.word node)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (previousCell : source.memory record=.word previous) :
    evaluateHOLFiniteState source (parentMetadata name)=
      (none,metadataState source node data.pointer data.length previous) := by
  have mapped0 : source.memaddrs record:=by simpa [byteAddress] using view.mapped source record db data 0 (by decide) (by decide)
  have mapped48 : source.memaddrs (record+48#64):=by simpa only [byteAddress] using view.mapped source record db data 48 (by decide) (by decide)
  have mapped56 : source.memaddrs (record+56#64):=by simpa only [byteAddress] using view.mapped source record db data 56 (by decide) (by decide)
  have pointerCell : source.memory (record+48#64)=.word data.pointer:=view.cells (48,data.pointer) (by cases payloadEq : data.payload <;> simp [WitnessRecord.Description.cells,payloadEq])
  have lengthCell : source.memory (record+56#64)=.word data.length:=view.cells (56,data.length) (by cases payloadEq : data.payload <;> simp [WitnessRecord.Description.cells,payloadEq])
  have mapped8 : source.memaddrs (node+8#64):=AllocatedBytes.word_mapped source node size 8 view.rows.domain nodeArena (by omega) nodeAligned (by decide)
  have mapped16 : source.memaddrs (node+16#64):=AllocatedBytes.word_mapped source node size 16 view.rows.domain nodeArena (by omega) nodeAligned (by decide)
  have recordUpper:=view.ceiling
  have nodeUpper:=nodeArena.upper
  have number8 : (node+8#64).toNat=node.toNat+8:=byteAddress_toNat node 8 (by omega)
  have number16 : (node+16#64).toNat=node.toNat+16:=byteAddress_toNat node 16 (by omega)
  have number56 : (record+56#64).toNat=record.toNat+56:=byteAddress_toNat record 56 (by omega)
  have away56 : record+56#64≠node+8#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number56,number8] at number; omega
  have away0a : record≠node+8#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number8] at number; omega
  have away0b : record≠node+16#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number16] at number; omega
  let first : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory (node+8#64) data.pointer}
  let second : PanSemStateFiniteExact 64 Guest.HostMemory:={first with memory:=StoreWord.put first.memory (node+16#64) data.length}
  let popped:=QueryBranch.bind second "top" previous
  have destination8 : eval source (.op .add [localVar name,.const 8#64])=some (.val (.word (node+8#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have pointerRead : eval source (readAt "top" 48#64)=some (.val (.word data.pointer)):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped48,pointerCell]
  have firstRun : evaluateHOLFiniteState source (writeAt name 8#64 (readAt "top" 48#64))=(none,first):=
    StoreWord.execute source _ _ _ _ destination8 pointerRead mapped8
  have destination16 : eval first (.op .add [localVar name,.const 16#64])=some (.val (.word (node+16#64))):=by
    simp [eval,first,evalHOLExact,evalListHOLExact,localVar,toExact,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have lengthRead : eval first (readAt "top" 56#64)=some (.val (.word data.length)):=by
    simp [eval,first,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped56,StoreWord.put,away56,lengthCell]
  have secondRun : evaluateHOLFiniteState first (writeAt name 16#64 (readAt "top" 56#64))=(none,second):=
    StoreWord.execute first _ _ _ _ destination16 lengthRead mapped16
  have previousRead : eval second (readAt "top" 0#64)=some (.val (.word previous)):=by
    simp [eval,second,first,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped0,StoreWord.put,away0a,away0b,previousCell]
  have popRun : evaluateHOLFiniteState second (.assign .local (ofString "top") (readAt "top" 0#64))=(none,popped):=
    StateSteps.assign_execute second "top" _ record previous topCell previousRead
  have poppedNode : popped.locals.lookup (ofString name)=some (.val (.word node)):=by
    exact (bind_lookup_other second "top" name previous different).trans nodeCell
  have poppedResult : popped.locals.lookup (ofString "result")=some (.val (.word oldResult)):=by
    exact (bind_lookup_other second "top" "result" previous (by decide)).trans resultCell
  have nodeRead : eval popped (localVar name)=some (.val (.word node)):=by simp [eval,evalHOLExact,localVar,toExact,poppedNode]
  have resultRun:=StateSteps.assign_execute popped "result" (localVar name) oldResult node poppedResult nodeRead
  unfold parentMetadata popWith
  rw [StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
    StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
    StateSteps.next_sequence second popped _ _ popRun (Nat.le_refl _)]
  exact resultRun

theorem metadata_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer length previous : BitVec 64) :
    let target:=metadataState source node pointer length previous
    target.locals.lookup (ofString "top")=some (.val (.word previous)) ∧
    target.locals.lookup (ofString "result")=some (.val (.word node)) ∧
    target.globals=source.globals ∧ target.memaddrs=source.memaddrs ∧ target.clock=source.clock := by
  exact ⟨bind_lookup_other _ "result" "top" node (by decide) |>.trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _,rfl,rfl,rfl⟩

theorem metadata_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer length previous query : BitVec 64)
    (away8 : query≠node+8#64) (away16 : query≠node+16#64) :
    (metadataState source node pointer length previous).memory query=source.memory query := by
  simp [metadataState,QueryBranch.bind,setVarHOLFinite,StoreWord.put,away8,away16]

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.parent_metadata_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.metadata_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.metadata_memory
