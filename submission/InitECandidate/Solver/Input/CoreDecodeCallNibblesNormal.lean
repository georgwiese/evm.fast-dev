import InitECandidate.Solver.Input.WitnessDecodeBodyNibblesNormal
import InitECandidate.Solver.Mpt.WitnessCoreDecodeProgram
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual continuing original core decode call derives its real
callee return/checked pair and d-bound continuation, complete physical
frame and fresh output ownership from unchanged original237. -/
theorem core_decode_call_nibbles_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputLower : 2713731432≤pointer.toNat) (below : cursor.toNat≤2713717616)
    (little : source.be=false) (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source Mpt.WitnessCore.decodeBranch=(none,post)) :
    ∃ built returned inner,
      let ready:=CallNormal.continuationEntry source built "d" returned
      Mpt.WitnessDecode.NormalFrame source ready heap cursor limit ∧
      Mpt.WitnessDecode.NibbleResult ready db pointer length heap cursor limit returned ∧
      ready.locals.lookup (ofString "d")=some returned ∧
      evaluateHOLFiniteState ready Mpt.WitnessCore.afterDecode=(none,inner) ∧ post=QueryBranch.restore source "d" inner := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Mpt.WitnessCore.decodeArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length)]:=by
    simp [Mpt.WitnessCore.decodeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,QueryBranch.localVar,toExact,dbCell,pointerCell,lengthCell]
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment source.code.lookup (ofString "_decode_step")
    (ofString "db") (ofString "p") (ofString "n") (Mpt.WitnessStep.body .decode) (.comb [.one,.one]) db pointer length
    (by decide) (by decide) (by decide) (Mpt.WitnessStep.original_code .decode source.code installed)
  rw [Mpt.WitnessCore.decode_shape] at normal
  obtain ⟨funded,built,returned,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source post "d" (.comb [.one,.one])
    (ofString "_decode_step") Mpt.WitnessCore.decodeArguments _ (Mpt.WitnessStep.body .decode) Mpt.WitnessCore.afterDecode callee (.comb [.one,.one]) args called normal
  let entry:=callEntryStateHOLFinite source callee
  have entryBoundary:=boundary.erase_frame input source entry rfl (dbLocal.trans dbCell.symm)
  have entryArena:=arena.of_fields source entry cursor limit rfl rfl
  obtain ⟨actualHeap,actualCell,heapArena,heapAligned,bodyFrame,result⟩:=decode_body_nibbles_normal input entry built db pointer length cursor limit entryBoundary dbLocal pointerLocal lengthLocal
    entryArena before small inputLower below little installed returned bodyRun
  have actualEq : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  let ready:=CallNormal.continuationEntry source built "d" returned
  have frame : Mpt.WitnessDecode.NormalFrame source ready heap cursor limit:=
    (bodyFrame.prefix source entry built heap cursor limit rfl rfl rfl (fun _=>rfl) (fun _ _=>rfl)).of_erase source ready built heap cursor limit rfl
  have readyResult:=result.of_fields built ready db pointer length heap cursor limit returned rfl rfl rfl rfl
  exact ⟨built,returned,inner,frame,readyResult,CallNormal.continuation_lookup_same _ _ _ _,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_decode_call_nibbles_normal
