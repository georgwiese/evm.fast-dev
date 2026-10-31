import InitECandidate.Solver.Mpt.CurrentWitnessDecodeStepFrame
import InitECandidate.Solver.Mpt.WitnessCoreDecodeProgram
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual continuing original core decode call derives its real
callee return/checked pair and d-bound continuation, complete physical
frame and fresh output ownership from the actual unchanged decoder. -/
theorem core_decode_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (dbBefore : db.toNat≤heap.toNat)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputLower : 2701131776≤pointer.toNat)
    (normal : evaluateHOLFiniteState source Mpt.WitnessCore.decodeBranch=(none,post)) :
    ∃ built returned inner,
      let ready:=CallNormal.continuationEntry source built "d" returned
      Mpt.WitnessDecode.LiveFrame source ready heap cursor limit ∧
      Mpt.WitnessDecode.NormalResult ready db pointer length heap cursor limit returned ∧
      ready.locals.lookup (ofString "d")=some returned ∧
      evaluateHOLFiniteState ready Mpt.WitnessCore.afterDecode=(none,inner) ∧ post=QueryBranch.restore source "d" inner := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Mpt.WitnessCore.decodeArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length)]:=by
    simp [Mpt.WitnessCore.decodeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,QueryBranch.localVar,toExact,dbCell,pointerCell,lengthCell]
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment source.code.lookup (ofString "_decode_step")
    (ofString "db") (ofString "p") (ofString "n") (Mpt.WitnessStep.body .decode) (.comb [.one,.one]) db pointer length
    (by decide) (by decide) (by decide) (Mpt.WitnessStep.original_code .decode source.code live.code)
  rw [Mpt.WitnessCore.decode_shape] at normal
  obtain ⟨funded,built,returned,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source post "d" (.comb [.one,.one])
    (ofString "_decode_step") Mpt.WitnessCore.decodeArguments _ (Mpt.WitnessStep.body .decode) Mpt.WitnessCore.afterDecode callee (.comb [.one,.one]) args called normal
  let entry:=callEntryStateHOLFinite source callee
  have entryArena:=arena.of_fields source entry cursor limit rfl rfl
  obtain ⟨bodyFrame,result⟩:=Mpt.WitnessDecode.current_step_frame entry built db pointer length heap cursor limit dbLocal pointerLocal lengthLocal
    small (before.trans dbBefore) heapCell heapArena heapBound heapAligned (live.of_frame rfl) entryArena dbBefore inputLower before returned bodyRun
  let ready:=CallNormal.continuationEntry source built "d" returned
  have frame:=Mpt.WitnessDecode.LiveFrame.of_erase entry built source ready heap cursor limit bodyFrame rfl rfl
  have readyResult:=result.of_fields built ready db pointer length heap cursor limit returned rfl rfl rfl
  exact ⟨built,returned,inner,frame,readyResult,CallNormal.continuation_lookup_same _ _ _ _,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_decode_call_normal
