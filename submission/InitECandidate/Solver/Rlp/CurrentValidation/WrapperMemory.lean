import InitECandidate.Solver.Rlp.CurrentValidation.Wrapper
import InitECandidate.Solver.Rlp.CurrentValidation.Memory
import InitECandidate.Solver.Input.CaughtCallStops
import InitECandidate.Solver.Input.NoReturnCaught
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.PureGuardNormal
import InitECandidate.Solver.Arenas.ScratchCallNormal

namespace InitECandidate.Solver.Rlp.CurrentValidate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem handler_stops : NoFallthrough handler :=
  NoFallthrough.sequence release _ (fun current=>raise_ne_none current _ _)
theorem handler_no_return : NoReturn.Never handler :=
  NoReturn.sequence release _ (NoReturn.ignored_call _ _) (NoReturn.raise _ _)
theorem caught_no_return : NoReturn.Never caught := NoReturn.caught_call _ _ _ _ _ handler_no_return

theorem caught_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (normal : evaluateHOLFiniteState source caught=(none,post)) :
    post.locals=source.locals ∧ LocalEffects.erase post=LocalEffects.erase source := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "_rlp_validate_items_body") Validation.body .one pointer length (Validation.original_code source.code arena.code)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  obtain ⟨funded,target,value,bodyRun,checked,restored⟩ := CallNormal.ignored_caught_stops source post (ofString "_rlp_validate_items_body") arguments _ Validation.body callee .one
    (ofString "RlpErr") (ofString "e") handler args called handler_stops normal
  have frame:=CurrentValidation.body_normal_frame (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits value bodyRun
  refine ⟨by rw [restored],?_⟩
  rw [restored]
  exact frame.2

theorem release_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source)
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word 2701127680#64)))
    (normal : evaluateHOLFiniteState source release=(none,post)) : LocalEffects.erase post=LocalEffects.erase source := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "mark"]=some [.val (.word 2701127680#64)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,markCell]
  obtain ⟨funded,released⟩ := Arenas.Scratch.release_call_normal source post 2701127680#64 2701127680#64 [localVar "mark"] args arena.scratch arena.code normal
  have sameGlobals : source.globals.update (ofString "scratch_ptr",.val (.word 2701127680#64))=source.globals := by
    apply HolFiniteMapExact.ext
    funext name
    by_cases same : name=ofString "scratch_ptr"
    · subst name
      simp [HolFiniteMapExact.update,FUPDATE,arena.scratch]
    · simp [HolFiniteMapExact.update,FUPDATE,same,Ne.symm same]
  rw [released]
  change LocalEffects.erase {source with globals:=source.globals.update (ofString "scratch_ptr",.val (.word 2701127680#64))}=LocalEffects.erase source
  rw [sameGlobals]

/-- The real public wrapper's normal return restores its actual mark and
preserves every nonlocal field, including memory, heap and both arenas. The
RLP handler cannot turn a stopped internal failure into a successful return. -/
theorem body_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ LocalEffects.erase post=LocalEffects.erase source := by
  rw [body_shape] at normal
  have funded:=CallNormal.normal_clock source post (ofString "mark") .one (ofString "scratch_mark") [] afterMark value normal
  have markRun:=Arenas.mark_call source .down "mark" 2701127680#64 afterMark (Arenas.Scratch.mark_code source.code arena.code) arena.scratch funded
  change evaluateHOLFiniteState source (.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark)=_ at markRun
  rw [markRun] at normal
  let marked:=bind {source with clock:=source.clock-1} "mark" 2701127680#64
  let markedInner:=(evaluateHOLFiniteState marked afterMark).2
  have observed:=congrArg Prod.fst normal
  change (evaluateHOLFiniteState marked afterMark).1=some (.returned value) at observed
  have continued : evaluateHOLFiniteState marked afterMark=(some (.returned value),markedInner) := Prod.ext observed rfl
  have postRestore : post=restore source "mark" markedInner := (congrArg Prod.snd normal).symm
  obtain ⟨errorInner,errorRun,errorRestore⟩ := declaration_return_word marked markedInner "e" (.const 0#64) 0#64 afterError value rfl continued
  let ready:=bind marked "e" 0#64
  have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other marked "e" "p" 0#64 (by decide)).trans ((bind_lookup_other {source with clock:=source.clock-1} "mark" "p" 2701127680#64 (by decide)).trans pointerCell)
  have readyLength : ready.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other marked "e" "len" 0#64 (by decide)).trans ((bind_lookup_other {source with clock:=source.clock-1} "mark" "len" 2701127680#64 (by decide)).trans lengthCell)
  have readyArena : CurrentStartup.ArenaState ready := arena.of_frame rfl
  obtain ⟨afterCaught,caughtRun,footerRun⟩ := sequence_returned ready errorInner caught (.seq release (.return (.const 0#64))) value (caught_no_return ready) errorRun
  obtain ⟨locals,caughtFrame⟩ := caught_normal_frame ready afterCaught pointer length readyPointer readyLength readyArena fits caughtRun
  obtain ⟨afterRelease,releaseRun,returnRun⟩ := sequence_returned afterCaught errorInner release (.return (.const 0#64)) value (NoReturn.ignored_call _ _ afterCaught) footerRun
  have markCell : afterCaught.locals.lookup (ofString "mark")=some (.val (.word 2701127680#64)) := by
    rw [locals]
    exact (bind_lookup_other marked "e" "mark" 0#64 (by decide)).trans (bind_lookup_same {source with clock:=source.clock-1} "mark" 2701127680#64)
  have releaseFrame:=release_normal_frame afterCaught afterRelease (readyArena.of_frame caughtFrame) markCell releaseRun
  obtain ⟨read,returned⟩ := return_normal afterRelease errorInner (.const 0#64) value returnRun
  have valueEq : value=.val (.word 0#64) := (Option.some.inj read).symm
  refine ⟨valueEq,?_⟩
  rw [postRestore,errorRestore,returned]
  exact releaseFrame.trans caughtFrame

end InitECandidate.Solver.Rlp.CurrentValidate

#print axioms InitECandidate.Solver.Rlp.CurrentValidate.caught_normal_frame
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.release_normal_frame
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.body_normal_frame
