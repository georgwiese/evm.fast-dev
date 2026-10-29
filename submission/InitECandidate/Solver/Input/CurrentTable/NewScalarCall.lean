import InitECandidate.Solver.Input.CurrentTable.NewScalarFrame
import InitECandidate.Solver.Input.AssignedCallKnown
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Each actual assigned table call in state_init returns its real fresh
header, preserves the original caller bindings, and carries the whole normal
persistent frame for the actual20/32/52-byte keys. -/
theorem scalar_local_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (key cap heap : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word key),.val (.word cap)])
    (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "htab_new") arguments)=(none,post)) :
    post.locals.lookup (ofString name)=some (.val (.word heap)) ∧
      (∀ other,ofString name≠ofString other→post.locals.lookup (ofString other)=source.locals.lookup (ofString other)) ∧
      AllocatedBytes.Arena heap 88 ∧ PersistentNormalFrame source post heap := by
  obtain ⟨callee,called,keyLocal,capLocal⟩:=word_pair_environment source.code.lookup (ofString "htab_new")
    (ofString "key_len") (ofString "cap") body .one key cap (by decide) (original_code source.code arena.code)
  obtain ⟨funded,target,answer,bodyRun,endpoint⟩:=CallNormal.local_known source post (ofString name) (ofString "htab_new") arguments _ body callee .one args called normal
  obtain ⟨answerEq,tableArena,frame⟩:=body_scalar_normal_frame (callEntryStateHOLFinite source callee) target heap key cap keyLocal capLocal atLeastTwo
    heapCell heapArena heapBound heapAligned (arena.of_frame rfl) answer bodyRun
  have callerFrame : PersistentNormalFrame source post heap:=frame.of_erase _ _ source post heap rfl (by rw [endpoint]; rfl)
  refine ⟨?_,?_,tableArena,callerFrame⟩
  · rw [endpoint,answerEq]
    exact CallNormal.continuation_lookup_same source target name _
  · intro other different
    rw [endpoint,answerEq]
    exact CallNormal.continuation_lookup_other source target name other (.val (.word heap)) different

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_local_normal_frame
