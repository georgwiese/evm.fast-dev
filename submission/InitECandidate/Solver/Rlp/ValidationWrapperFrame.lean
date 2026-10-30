import InitECandidate.Solver.Rlp.ValidationCaughtFrame
import InitECandidate.Solver.Arenas.ScratchCallNormal

namespace InitECandidate.Solver.Rlp.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The public original wrapper restores its saved cursor and preserves
every ordinary word above that cursor through its actual normal return. -/
theorem body_normal_outside (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ Validation.Arena target cursor limit ∧ Validation.Outside source target limit.toNat cursor.toNat := by
  rw [body_shape] at normal
  have raw : lookupCodeHOLExact source.code.lookup (ofString "scratch_mark") []=some (Arenas.markBody .down,(fun _=>none),.one) := by
    simp [lookupCodeHOLExact,Arenas.Scratch.mark_code source.code installed]
  obtain ⟨callee,called,locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup source.code.lookup (ofString "scratch_mark") [] (Arenas.markBody .down) (fun _=>none) .one raw
  have positive := (Input.CallNormal.scoped_normal source target "mark" .one (ofString "scratch_mark") [] [] (Arenas.markBody .down) afterMark callee .one rfl called value normal).1
  have actual := Arenas.mark_call source .down "mark" cursor afterMark (Arenas.Scratch.mark_code source.code installed) arena.cursorGlobal positive
  change evaluateHOLFiniteState source (.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark)=_ at actual
  rw [actual] at normal
  let marked := bind {source with clock:=source.clock-1} "mark" cursor
  let markedInner := (evaluateHOLFiniteState marked afterMark).2
  have firstEq := congrArg Prod.fst normal
  change (evaluateHOLFiniteState marked afterMark).1=some (.returned value) at firstEq
  have continued : evaluateHOLFiniteState marked afterMark=(some (.returned value),markedInner) := Prod.ext firstEq rfl
  have targetRestore : target=restore source "mark" markedInner := (congrArg Prod.snd normal).symm
  obtain ⟨errorInner,errorRun,errorRestore⟩ := Input.declaration_return_word marked markedInner "e" (.const 0#64) 0#64 afterError value rfl continued
  let ready := bind marked "e" 0#64
  have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ "e" "p" _ (by decide)).trans ((bind_lookup_other _ "mark" "p" _ (by decide)).trans pointerCell)
  have readyLength : ready.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other _ "e" "len" _ (by decide)).trans ((bind_lookup_other _ "mark" "len" _ (by decide)).trans lengthCell)
  have readyArena := Validation.Arena.of_fields source ready cursor limit arena rfl rfl
  obtain ⟨afterCaught,caughtRun,footerRun⟩ := Input.sequence_returned ready errorInner caught (.seq release (.return (.const 0#64))) value (caught_no_return ready) errorRun
  obtain ⟨callerLocals,nextCursor,nextArena,decreases,above⟩ := caught_normal_outside ready afterCaught pointer length cursor limit readyPointer readyLength readyArena fits installed caughtRun
  obtain ⟨afterRelease,releaseRun,returnRun⟩ := Input.sequence_returned afterCaught errorInner release (.return (.const 0#64)) value
    (Input.NoReturn.ignored_call _ _ afterCaught) footerRun
  have markCell : afterCaught.locals.lookup (ofString "mark")=some (.val (.word cursor)) := by
    rw [callerLocals]
    exact (bind_lookup_other _ "e" "mark" _ (by decide)).trans (bind_lookup_same _ _ _)
  have releaseArgs : evalListHOLFinite afterCaught (h:=fun address=>Classical.propDecidable (afterCaught.memaddrs address)) [localVar "mark"]=some [.val (.word cursor)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,markCell]
  have caughtCode : afterCaught.code=source.code := (Input.evaluation_fields ready afterCaught caught none caughtRun).2.2.2
  obtain ⟨releasePositive,released⟩ := Arenas.Scratch.release_call_normal afterCaught afterRelease cursor nextCursor [localVar "mark"] releaseArgs nextArena.cursorGlobal
    (by rw [caughtCode]; exact installed) releaseRun
  have releasedArena : Validation.Arena afterRelease cursor limit := by
    rw [released]
    refine ⟨nextArena.domain,?_,?_,arena.ordered,arena.aligned,arena.lower,arena.upper⟩
    · simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE]
    · simpa [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE,
        show ofString "scratch_ptr"≠ofString "frame_mem_ptr" from by decide] using nextArena.limitGlobal
  obtain ⟨read,returned⟩ := Input.return_normal afterRelease errorInner (.const 0#64) value returnRun
  refine ⟨(Option.some.inj read).symm,Validation.Arena.of_fields afterRelease target cursor limit releasedArena ?_ ?_,?_⟩
  · rw [targetRestore,errorRestore,returned]
    rfl
  · rw [targetRestore,errorRestore,returned]
    rfl
  · refine ⟨?_, ?_⟩
    · rw [targetRestore,errorRestore,returned,released]
      exact above.runtime
    · intro query upper
      rw [targetRestore,errorRestore,returned,released]
      exact above query upper


theorem body_normal_above (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ Validation.Arena target cursor limit ∧ Validation.Above source target cursor.toNat := by
  obtain ⟨returned,arena',outside⟩ := body_normal_outside source target pointer length cursor limit pointerCell lengthCell arena fits installed value normal
  exact ⟨returned,arena',fun query beyond=>outside query (Or.inr beyond)⟩

end InitECandidate.Solver.Rlp.Validate

#print axioms InitECandidate.Solver.Rlp.Validate.body_normal_outside

#print axioms InitECandidate.Solver.Rlp.Validate.body_normal_above
