import InitECandidate.Solver.Input.CurrentTable.NodeBuild.StateTransport
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.LoopReads
import InitECandidate.Solver.Input.CurrentTable.FirstDiff.MemoryKey
import InitECandidate.Solver.Input.CurrentTable.Set.CallCost
import InitECandidate.Solver.Input.CurrentTable.Set.CallReturned

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem set_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (inside : index<data.total) :
    source.clock-(evaluateHOLFiniteState source setCall).2.clock≤816 := by
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bound⟩ := state.image
  exact Set.call_cost source data.table data.cap root data.out (byteAddress data.array (16*index)) next count valid bits left right keys
    (FirstDiff.memoryKey source data.out) (ValueOf data) image (image.two_available index data.total bound inside layout.capacity)
    (FirstDiff.memoryKey_view source data.out state.arena.domain layout.outArena) ⟨index,inside,rfl⟩ state.arena.code state.little layout.outAligned
    (by have a:=layout.outBefore; have b:=layout.lowerUpper; have c:=layout.inputBefore; omega) (some none) setArguments
    (set_arguments data origin source index state)

/-- A real insertion return and the original counter increment produce the
next physical loop state, including genuine witness-value membership. -/
theorem set_increment_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (inside : index<data.total)
    (run : evaluateHOLFiniteState source (.seq setCall increment)=(none,post)) : State data origin post (index+1) := by
  obtain ⟨middle,setRun,incrementRun⟩ := sequence_none source post setCall increment run
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bound⟩ := state.image
  obtain ⟨result,locals⟩ := Set.call_returned source middle data.table data.cap root data.out (byteAddress data.array (16*index))
    next count valid bits left right keys (FirstDiff.memoryKey source data.out) (ValueOf data) image
    (image.two_available index data.total bound inside layout.capacity) (by have := layout.capacity; omega)
    (FirstDiff.memoryKey_view source data.out state.arena.domain layout.outArena) ⟨index,inside,rfl⟩ state.arena.code state.little layout.outAligned
    (by have a:=layout.outBefore; have b:=layout.lowerUpper; have c:=layout.inputBefore; omega)
    setArguments (set_arguments data origin source index state) setRun
  have middleIndex : middle.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) := by rw [locals]; exact state.indexCell
  have nextRead : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,middleIndex,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have incremented := StateSteps.assign_execute middle "i" (.op .add [localVar "i",.const 1#64])
    (BitVec.ofNat 64 index) (BitVec.ofNat 64 (index+1)) middleIndex nextRead
  change evaluateHOLFiniteState middle increment=(none,bind middle "i" (BitVec.ofNat 64 (index+1))) at incremented
  rw [incremented] at incrementRun
  have endpoint : post=bind middle "i" (BitVec.ofNat 64 (index+1)) := (congrArg Prod.snd incrementRun).symm
  subst post
  have globals := congrArg PanSemStateFiniteExact.globals result.metadata
  change middle.globals=source.globals at globals
  have localsKept (key : MlS) (different : ofString "i"≠key) :
      (bind middle "i" (BitVec.ofNat 64 (index+1))).locals.lookup key=source.locals.lookup key := by
    simp [WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,locals]
  obtain ⟨newRoot,newNext,newCount,newValid,newBits,newLeft,newRight,newKeys,nextImage,countBound⟩ := result.image
  apply state.transport data origin source (bind middle "i" (BitVec.ofNat 64 (index+1))) index (index+1) (MemoryMetadata.code result.metadata)
    (MemoryMetadata.domain result.metadata) (MemoryMetadata.endian result.metadata)
    (fun key=>congrArg (fun table=>table.lookup key) globals) localsKept
    ⟨by intro query lower upper; exact result.before query (by have := layout.inputBefore; omega)⟩
    (bind_lookup_same _ _ _)
  exact ⟨newRoot,newNext,newCount,newValid,newBits,newLeft,newRight,newKeys,nextImage.of_frame rfl,by omega⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.set_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.set_increment_normal
