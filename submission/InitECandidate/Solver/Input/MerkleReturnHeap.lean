import InitECandidate.Solver.Input.MerkleGlobals
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem ignored_never (function : MlS) (arguments : List (ExpHOL 64)) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) :
    (evaluateHOLFiniteState source (.call (some (none,none)) function arguments)).1≠some (.returned value) :=
  ((LocalPrefix.call (key:=ofString "mark") none function arguments (by intro name impossible; cases impossible)).summary_full source).2.1 value

/-- A real normal output suffix executes the original release with the
saved mark. Normality derives its funding; no successful release is assumed. -/
theorem output_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterExtension=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  rw [extension_shape.2.2.2] at run
  obtain ⟨copied,copyRun,remaining⟩ := sequence_returned source post _ _ value (ignored_never _ _ source) run
  have copyLocals := (LocalPrefix.call (key:=ofString "mark") none (ofString "memcpy") outputArguments (by intro name impossible; cases impossible)).summary_full source
  unfold LocalSummary at copyLocals
  simp only [Option.map_none] at copyLocals
  rw [copyRun] at copyLocals
  have copiedMark : copied.locals.lookup (ofString "mark")=some (.val (.word mark)) := (copyLocals.1 rfl).trans saved
  have copyGlobals := GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "memcpy") outputArguments
    CopyGeneral.formals Copy32.body .one (CopyGeneral.original_code source.code installed) (Copy32.globals (ofString "heap_ptr") source.code) source rfl
  change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") outputArguments)).2=GlobalEffects.erase (ofString "heap_ptr") source at copyGlobals
  rw [copyRun] at copyGlobals
  have copiedHeap : copied.globals.lookup (ofString "heap_ptr")=some (.val (.word old)) := (congrArg Prod.snd copyGlobals).trans heap
  have fields := evaluation_fields source copied _ none copyRun
  have copiedInstalled : OriginalCode.Installed copied.code := fields.2.2.2.symm ▸ installed
  obtain ⟨released,releaseRun,returned⟩ := sequence_returned copied post _ _ value (ignored_never _ _ copied) remaining
  have funded := (CallNormal.ignored_data copied released (ofString "heap_release") [localVar "mark"] releaseRun).1
  have args : evalListHOLFinite copied (h:=fun address=>Classical.propDecidable (copied.memaddrs address)) [localVar "mark"]=some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,copiedMark]
  have actual := HeapScope.release_call_execute copied mark old [localVar "mark"] args copiedHeap
    (HeapScope.release_original_code copied.code copiedInstalled) funded
  rw [releaseRun] at actual
  have endpoint : released=HeapScope.releasePost {copied with clock:=copied.clock-1} mark := congrArg Prod.snd actual
  have postEq : post=emptyLocalsHOLFinite released := by
    have actualReturn : evaluateHOLFiniteState released (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite released) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [actualReturn] at returned
    exact (congrArg Prod.snd returned).symm
  rw [postEq]
  change released.globals.lookup (ofString "heap_ptr")=_
  rw [endpoint]
  simp [HeapScope.releasePost,HolFiniteMapExact.lookup_update,FUPDATE]

/-- Dense and extension loops preserve their actual heap/mark; the real
normal suffix then restores the saved cursor. This says nothing about
cryptographic output contents. -/
theorem dense_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dn : Nat) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (depth : source.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source denseContinuation=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  rw [outer_shape.2.2] at run
  obtain ⟨halved,halvedRun,remaining⟩ := sequence_returned source post outerLoop afterDense value
    ((outer_loop_other (ofString "mark") (by decide) (by decide) (by decide)).summary_full source).2.1 run
  have halvedOther (name : String) (a : ofString name≠ofString "cur") (b : ofString name≠ofString "half") (c : ofString name≠ofString "j") :
      halved.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary := (outer_loop_other (ofString name) a b c).summary_full source
    unfold LocalSummary at summary
    rw [halvedRun] at summary
    exact summary.1 rfl
  have halvedGlobal := outer_loop_globals (ofString "heap_ptr") source.code installed source rfl
  rw [halvedRun] at halvedGlobal
  have halvedHeap := (congrArg Prod.snd halvedGlobal).trans heap
  have fields := evaluation_fields source halved outerLoop none halvedRun
  have halvedInstalled : OriginalCode.Installed halved.code := fields.2.2.2.symm ▸ installed
  have read : eval halved (localVar "dn")=some (.val (.word (BitVec.ofNat 64 dn))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using (halvedOther "dn" (by decide) (by decide) (by decide)).trans depth
  rw [extension_shape.1] at remaining
  obtain ⟨inner,innerRun,endpoint⟩ := declaration_return_word halved post "d" (localVar "dn") (BitVec.ofNat 64 dn) _ value read remaining
  let entry := bind halved "d" (BitVec.ofNat 64 dn)
  obtain ⟨extended,extensionRun,outputRun⟩ := sequence_returned entry inner extensionLoop afterExtension value
    ((extension_loop_other (ofString "mark") (by decide)).summary_full entry).2.1 innerRun
  have extensionLocals := (extension_loop_other (ofString "mark") (by decide)).summary_full entry
  unfold LocalSummary at extensionLocals
  rw [extensionRun] at extensionLocals
  have entryMark : entry.locals.lookup (ofString "mark")=some (.val (.word mark)) :=
    (bind_lookup_other halved "d" "mark" (BitVec.ofNat 64 dn) (by decide)).trans ((halvedOther "mark" (by decide) (by decide) (by decide)).trans saved)
  have extendedMark := (extensionLocals.1 rfl).trans entryMark
  have extensionGlobals := extension_loop_globals (ofString "heap_ptr") entry.code halvedInstalled entry rfl
  rw [extensionRun] at extensionGlobals
  have extendedHeap := (congrArg Prod.snd extensionGlobals).trans halvedHeap
  have nextFields := evaluation_fields entry extended extensionLoop none extensionRun
  have extendedInstalled : OriginalCode.Installed extended.code := nextFields.2.2.2.symm ▸ halvedInstalled
  have restored := output_return_heap extended inner mark old extendedInstalled extendedMark extendedHeap value outputRun
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.output_return_heap
#print axioms InitECandidate.Solver.Input.Merkle.dense_return_heap
