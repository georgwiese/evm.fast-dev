import InitECandidate.Solver.Mpt.CurrentWitnessDecodeStepFrame
import InitECandidate.Solver.Mpt.CurrentWitnessCoreDecode
import InitECandidate.Solver.Mpt.CurrentWitnessCoreCost
import InitECandidate.Solver.Input.LoopNormal
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.WitnessCore
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem current_decode_branch_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap oldResult oldMode : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) :
    ∃ node,(node=0#64 ∨ heap.toNat≤node.toNat ∧ node.toNat≤2952790016) ∧
      post.locals.lookup (ofString "result")=some (.val (.word node)) ∧ PersistentNormalFrame source post heap := by
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=current_decode_environment source db pointer length arena.code
  rw [decode_shape] at normal
  obtain ⟨funded,target,value,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source post "d" (.comb [.one,.one])
    (ofString "_decode_step") decodeArguments _ (WitnessStep.body .decode) afterDecode callee (.comb [.one,.one])
    (current_decode_arguments source db pointer length dbCell pointerCell lengthCell) called normal
  obtain ⟨result,frame⟩:=WitnessDecode.current_step_frame (callEntryStateHOLFinite source callee) target db pointer length heap dbLocal pointerLocal lengthLocal
    small before heapCell heapArena heapBound aligned (arena.of_frame rfl) value bodyRun
  obtain ⟨node,valueEq,bounds⟩:=result
  rw [valueEq] at continued
  let ready:=CallNormal.continuationEntry source target "d" (.rStruct [.val (.word 0#64),.val (.word node)])
  have dCell : ready.locals.lookup (ofString "d")=some (.rStruct [.val (.word 0#64),.val (.word node)]):=CallNormal.continuation_lookup_same _ _ _ _
  have currentResult : ready.locals.lookup (ofString "result")=some (.val (.word oldResult)):=
    (CallNormal.continuation_lookup_other source target "d" "result" _ (by decide)).trans resultCell
  have currentMode : ready.locals.lookup (ofString "mode")=some (.val (.word oldMode)):=
    (CallNormal.continuation_lookup_other source target "d" "mode" _ (by decide)).trans modeCell
  rw [after_decode_zero_choice ready _ dCell,terminal_execute ready node oldResult oldMode dCell currentResult currentMode] at continued
  have middleEq : inner=delivered ready node:=(congrArg Prod.snd continued).symm
  have callerFrame : PersistentNormalFrame source ready heap:=frame.of_erase _ _ source ready heap rfl rfl
  have physical : LocalEffects.erase post=LocalEffects.erase ready:=by rw [endpoint,middleEq]; rfl
  refine ⟨node,bounds,?_,callerFrame.of_erase source ready source post heap rfl physical⟩
  rw [endpoint,middleEq,restore_lookup_other source _ "d" "result" (by decide)]
  exact (delivered_fields ready node).1

theorem current_condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (go : BitVec 64)
    (cell : source.locals.lookup (ofString "go")=some (.val (.word go))) :
    eval source condition=some (.val (.word (if go=0#64 then 0#64 else 1#64))) := by
  simp [eval,condition,evalHOLExact,localVar,toExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- The actual normal loop executes its real first decode and final
empty-stack return iteration. Both normal physical frames are retained. -/
theorem current_loop_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64) (entry : CurrentDecodeEntry source db pointer length heap)
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source (.while condition loopBody)=(none,post)) :
    ∃ node,(node=0#64 ∨ heap.toNat≤node.toNat ∧ node.toNat≤2952790016) ∧
      post.locals.lookup (ofString "result")=some (.val (.word node)) ∧ PersistentNormalFrame source post heap := by
  have read : eval source condition=some (.val (.word 1#64)):=by simpa using current_condition_read source 1#64 entry.goCell
  obtain ⟨funded,middle,bodyRun,tailRun,clock⟩:=while_none_step source post (ofString "db") condition loopBody loop_body_prefix read normal
  rw [loop_body_choice (decClockHOLFinite source) 1#64 entry.modeCell,if_pos rfl] at bodyRun
  obtain ⟨node,bounds,resultCell,frame⟩:=current_decode_branch_frame (decClockHOLFinite source) middle db pointer length heap 0#64 1#64
    entry.dbCell entry.pointerCell entry.lengthCell entry.resultCell entry.modeCell small before entry.heapCell heapArena heapBound aligned (entry.arena.of_frame rfl) bodyRun
  obtain ⟨modeCell,topCell,goCell⟩:=current_decode_branch_none (decClockHOLFinite source) middle db pointer length heap 0#64 1#64
    entry.dbCell entry.pointerCell entry.lengthCell entry.resultCell entry.modeCell entry.topCell entry.goCell small before
    entry.heapCell heapArena heapBound aligned (entry.arena.of_frame rfl) bodyRun
  have nextRead : eval middle condition=some (.val (.word 1#64)):=by simpa using current_condition_read middle 1#64 goCell
  obtain ⟨nextFunded,last,lastRun,doneRun,lastClock⟩:=while_none_step middle post (ofString "db") condition loopBody loop_body_prefix nextRead tailRun
  rw [current_finish_execute (decClockHOLFinite middle) 1#64 ⟨modeCell,topCell,goCell⟩] at lastRun
  have lastEq : last=bind (decClockHOLFinite middle) "go" 0#64:=(congrArg Prod.snd lastRun).symm
  have inactive : evalHOLFinite last (h:=fun query=>Classical.propDecidable (last.memaddrs query)) condition=some (.val (.word 0#64)) := by
    change eval last condition=some (.val (.word 0#64))
    rw [lastEq]
    simpa using current_condition_read (bind (decClockHOLFinite middle) "go" 0#64) 0#64 (bind_lookup_same _ _ _)
  rw [evaluateHOLFiniteState_while_total,inactive] at doneRun
  have postEq : post=last:=by simpa using (congrArg Prod.snd doneRun).symm
  have physical : LocalEffects.erase post=LocalEffects.erase middle:=by rw [postEq,lastEq]; rfl
  refine ⟨node,bounds,?_,frame.of_erase (decClockHOLFinite source) middle source post heap rfl physical⟩
  rw [postEq,lastEq]
  exact (bind_lookup_other (decClockHOLFinite middle) "go" "result" 0#64 (by decide)).trans resultCell

/-- Whole unchanged current236 normal return: the original terminal word,
its zero/fresh bounds and complete persistent/input/runtime frame survive all
seven real local scopes, both loop iterations and the result footer. -/
theorem current_body_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ node,value=.val (.word node) ∧ (node=0#64 ∨ heap.toNat≤node.toNat ∧ node.toNat≤2952790016) ∧ PersistentNormalFrame source post heap := by
  obtain ⟨restoreStack,inner,setup,continued,endpoint,clock⟩:=initial_trace source post pointer length pointerCell lengthCell _ normal
  let entered:=ready source pointer length
  have safe : LocalPrefix (ofString "db") (.while condition loopBody):=.loop condition loop_body_prefix
  obtain ⟨middle,loopRun,footerRun,preserved⟩:=safe.normal_continue entered inner footer value continued
  obtain ⟨node,bounds,resultCell,frame⟩:=current_loop_normal_frame entered middle db pointer length heap
    (current_initial_entry source db pointer length heap dbCell heapCell arena) small before heapArena heapBound aligned loopRun
  obtain ⟨read,innerEq⟩:=return_normal middle inner (localVar "result") value footerRun
  have expected : eval middle (localVar "result")=some (.val (.word node)):=by simp [eval,evalHOLExact,localVar,toExact,resultCell]
  have valueEq : value=.val (.word node):=Option.some.inj (read.symm.trans expected)
  have restored:=ProgramPrefix.restoration_frame setup inner
  have physical:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) restored
  change LocalEffects.erase (restoreStack inner)=LocalEffects.erase inner at physical
  have exit : LocalEffects.erase post=LocalEffects.erase middle:=by rw [endpoint]; rw [physical,innerEq]; rfl
  exact ⟨node,valueEq,bounds,frame.of_erase entered middle source post heap rfl exit⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_decode_branch_frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_loop_normal_frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_body_normal_frame
