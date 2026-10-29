import InitECandidate.Solver.Mpt.CurrentWitnessCoreFrame
import InitECandidate.Solver.Mpt.CurrentWitnessMaterializeCost
import InitECandidate.Solver.Arenas.ScratchCallNormal
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.NoReturnCaught
import InitECandidate.Solver.Input.CaughtAssignedStops
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.NormalCallClock

namespace InitECandidate.Solver.Mpt.WitnessWrapper
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem seeded_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.dec (ofString "e") .one (.const 0#64)
      (.dec (ofString "nd") .one (.const 0#64) continuation))=(some (.returned value),post)) :
    ∃ inner,evaluateHOLFiniteState (seeded source) continuation=(some (.returned value),inner) ∧
      LocalEffects.erase post=LocalEffects.erase inner := by
  obtain ⟨middle,firstRun,firstEnd⟩:=ScalarScope.declare_trace source post "e" (.const 0#64) 0#64 _ _ rfl normal
  obtain ⟨inner,continued,secondEnd⟩:=ScalarScope.declare_trace (bind source "e" 0#64) middle "nd" (.const 0#64) 0#64 continuation _ rfl firstRun
  exact ⟨inner,continued,by rw [firstEnd,secondEnd]; rfl⟩

end InitECandidate.Solver.Mpt.WitnessWrapper

namespace InitECandidate.Solver.Mpt.WitnessMaterializeMpt
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A normal catch-wrapper return comes from the same genuine decoder-body
return; release-and-rethrow cannot manufacture successful fallthrough. -/
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
  rw [wrapper_shape,afterError] at normal
  obtain ⟨inner,continued,endpoint⟩:=WitnessWrapper.seeded_trace source post afterResult value normal
  let ready:=WitnessWrapper.seeded source
  have handlerNever : NoReturn.Never handler:=NoReturn.sequence _ _ (NoReturn.ignored_call _ _) (NoReturn.raise _ _)
  have caughtNever : NoReturn.Never caught:=NoReturn.caught_destination _ _ _ _ _ _ handlerNever
  obtain ⟨middle,caughtRun,footerRun⟩:=Input.sequence_returned ready inner caught footer value (caughtNever ready) continued
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment ready.code.lookup
    (ofString "_decode_witness_node_body") (ofString "db") (ofString "p") (ofString "n") WitnessCore.body .one
    db pointer length (by decide) (by decide) (by decide) (WitnessCore.original_code source.code arena.code)
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) childArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length)] := by
    have dbReady:=(WitnessWrapper.seeded_other source "db" (by decide) (by decide)).trans dbCell
    have pointerReady:=(WitnessWrapper.seeded_other source "p" (by decide) (by decide)).trans pointerCell
    have lengthReady:=(WitnessWrapper.seeded_other source "n" (by decide) (by decide)).trans lengthCell
    simp [ready,childArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbReady,pointerReady,lengthReady]
  have handlerStops : NoFallthrough handler:=NoFallthrough.sequence _ _ (NoFallthrough.raised _ _)
  obtain ⟨funded,target,answer,bodyRun,checked,callerEnd⟩:=CallNormal.assigned_caught_stops ready middle (ofString "nd")
    (ofString "_decode_witness_node_body") childArguments _ WitnessCore.body callee .one (ofString "MptErr") (ofString "e") handler args called
    (fun current _=>handlerStops current) caughtRun
  obtain ⟨node,answerEq,bounds,frame⟩:=WitnessCore.current_body_normal_frame (callEntryStateHOLFinite ready callee) target db pointer length heap
    dbLocal pointerLocal lengthLocal small before heapCell heapArena heapBound aligned (arena.of_frame rfl) answer bodyRun
  have currentFrame : PersistentNormalFrame ready middle heap:=frame.of_erase _ _ ready middle heap rfl (by rw [callerEnd]; rfl)
  obtain ⟨read,innerEq⟩:=return_normal middle inner (localVar "nd") value footerRun
  have nodeCell : middle.locals.lookup (ofString "nd")=some (.val (.word node)) := by
    rw [callerEnd,answerEq]
    exact CallNormal.continuation_lookup_same ready target "nd" _
  have expected : eval middle (localVar "nd")=some (.val (.word node)):=by simp [eval,evalHOLExact,localVar,toExact,nodeCell]
  have physical : LocalEffects.erase post=LocalEffects.erase middle:=by rw [endpoint,innerEq]; rfl
  exact ⟨node,Option.some.inj (read.symm.trans expected),bounds,currentFrame.of_erase ready middle source post heap rfl physical⟩

end InitECandidate.Solver.Mpt.WitnessMaterializeMpt

#print axioms InitECandidate.Solver.Mpt.WitnessWrapper.seeded_trace
#print axioms InitECandidate.Solver.Mpt.WitnessMaterializeMpt.current_body_normal_frame
