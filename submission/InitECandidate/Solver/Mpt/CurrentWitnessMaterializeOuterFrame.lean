import InitECandidate.Solver.Mpt.CurrentWitnessMaterializeFrame

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real release on a successful outer-wrapper path restores its actual
entry mark. Both caught handlers rethrow and cannot supply a normal result. -/
theorem current_after_mark_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap mark : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (cursor : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word mark)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) :
    ∃ node,value=.val (.word node) ∧ (node=0#64 ∨ heap.toNat≤node.toNat ∧ node.toNat≤2952790016) ∧ PersistentNormalFrame source post heap := by
  obtain ⟨inner,continued,endpoint⟩:=WitnessWrapper.seeded_trace source post afterResult value normal
  let ready:=WitnessWrapper.seeded source
  have handlerNever : NoReturn.Never handler:=NoReturn.sequence _ _ (NoReturn.ignored_call _ _) (NoReturn.raise _ _)
  have caughtNever : NoReturn.Never caught:=NoReturn.caught_destination _ _ _ _ _ _ handlerNever
  obtain ⟨middle,caughtRun,footerRun⟩:=Input.sequence_returned ready inner caught footer value (caughtNever ready) continued
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal,markLocal⟩:=word_quad_environment ready.code.lookup
    (ofString "_decode_witness_node_mpt") (ofString "db") (ofString "p") (ofString "n") (ofString "mark") WitnessMaterializeMpt.body .one
    db pointer length mark (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (WitnessMaterializeMpt.original_code source.code arena.code)
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) childArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length),.val (.word mark)] := by
    have dbReady:=(WitnessWrapper.seeded_other source "db" (by decide) (by decide)).trans dbCell
    have pointerReady:=(WitnessWrapper.seeded_other source "p" (by decide) (by decide)).trans pointerCell
    have lengthReady:=(WitnessWrapper.seeded_other source "n" (by decide) (by decide)).trans lengthCell
    have markReady:=(WitnessWrapper.seeded_other source "mark" (by decide) (by decide)).trans markCell
    simp [ready,childArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbReady,pointerReady,lengthReady,markReady]
  have handlerStops : NoFallthrough handler:=NoFallthrough.sequence _ _ (NoFallthrough.raised _ _)
  obtain ⟨funded,target,answer,bodyRun,checked,callerEnd⟩:=CallNormal.assigned_caught_stops ready middle (ofString "nd")
    (ofString "_decode_witness_node_mpt") childArguments _ WitnessMaterializeMpt.body callee .one (ofString "RlpErr") (ofString "e") handler args called
    (fun current _=>handlerStops current) caughtRun
  obtain ⟨node,answerEq,bounds,frame⟩:=WitnessMaterializeMpt.current_body_normal_frame (callEntryStateHOLFinite ready callee) target db pointer length heap
    dbLocal pointerLocal lengthLocal small before heapCell heapArena heapBound aligned (arena.of_frame rfl) answer bodyRun
  have currentFrame : PersistentNormalFrame ready middle heap:=frame.of_erase _ _ ready middle heap rfl (by rw [callerEnd]; rfl)
  have nodeCell : middle.locals.lookup (ofString "nd")=some (.val (.word node)) := by
    rw [callerEnd,answerEq]
    exact CallNormal.continuation_lookup_same ready target "nd" _
  have markReady : ready.locals.lookup (ofString "mark")=some (.val (.word mark)):=
    (WitnessWrapper.seeded_other source "mark" (by decide) (by decide)).trans markCell
  have currentMark : middle.locals.lookup (ofString "mark")=some (.val (.word mark)):=by
    rw [callerEnd]
    exact (CallNormal.continuation_lookup_other ready target "nd" "mark" answer (by decide)).trans markReady
  have currentCursor : middle.globals.lookup (ofString "scratch_ptr")=some (.val (.word mark)):=
    (currentFrame.globals _ (by decide)).trans cursor
  have currentArena:=currentFrame.current_arena (arena.of_frame rfl)
  obtain ⟨released,releaseRun,returnRun⟩:=Input.sequence_returned middle inner release (.return (localVar "nd")) value
    (NoReturn.ignored_call _ _ middle) footerRun
  have releaseArgs : evalListHOLFinite middle (h:=fun query=>Classical.propDecidable (middle.memaddrs query)) [localVar "mark"]=some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,currentMark]
  have releasedEq:=Arenas.Scratch.release_same_call_normal middle released mark [localVar "mark"] releaseArgs currentCursor currentArena.code releaseRun
  obtain ⟨read,innerEq⟩:=return_normal released inner (localVar "nd") value returnRun
  have expected : eval released (localVar "nd")=some (.val (.word node)):=by
    rw [releasedEq]
    simp [eval,evalHOLExact,localVar,toExact,nodeCell]
  have physical : LocalEffects.erase post=LocalEffects.erase middle:=by rw [endpoint,innerEq,releasedEq]; rfl
  exact ⟨node,Option.some.inj (read.symm.trans expected),bounds,currentFrame.of_erase ready middle source post heap rfl physical⟩

/-- Whole unchanged238 normal return, including the genuine mark call,
restored scratch cursor, advanced heap and protection of every earlier word. -/
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
  rw [wrapper_shape] at normal
  have funded:=CallNormal.normal_clock source post (ofString "mark") .one (ofString "scratch_mark") [] afterMark value normal
  have marked:=Arenas.mark_call source .down "mark" 2701127680#64 afterMark (Arenas.Scratch.mark_code source.code arena.code) arena.scratch funded
  simp only [Arenas.markName] at marked
  rw [marked] at normal
  let ready:=bind {source with clock:=source.clock-1} "mark" 2701127680#64
  let inner:=(evaluateHOLFiniteState ready afterMark).2
  have observed:=congrArg Prod.fst normal
  change (evaluateHOLFiniteState ready afterMark).1=some (.returned value) at observed
  have continued : evaluateHOLFiniteState ready afterMark=(some (.returned value),inner):=Prod.ext observed rfl
  have endpoint : post=restore source "mark" inner:=(congrArg Prod.snd normal).symm
  obtain ⟨node,valueEq,bounds,frame⟩:=current_after_mark_normal_frame ready inner db pointer length heap 2701127680#64
    ((bind_lookup_other _ "mark" "db" _ (by decide)).trans dbCell)
    ((bind_lookup_other _ "mark" "p" _ (by decide)).trans pointerCell)
    ((bind_lookup_other _ "mark" "n" _ (by decide)).trans lengthCell) (bind_lookup_same _ _ _) arena.scratch
    small before heapCell heapArena heapBound aligned (arena.of_frame rfl) value continued
  exact ⟨node,valueEq,bounds,frame.of_erase ready inner source post heap rfl (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.current_after_mark_normal_frame
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.current_body_normal_frame
