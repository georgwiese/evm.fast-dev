import InitECandidate.Solver.Mpt.LookupGlobals
import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem finish_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source finish=(some (.returned returned),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have safe : Input.LocalPrefix (ofString "r") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,released,tailRun,locals⟩ := safe.normal_continue source post (.return (localVar "r")) returned normal
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "mark"]=some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,markCell]
  have releaseCode := Input.HeapScope.release_original_code source.code installed
  obtain ⟨callee,called,m⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "heap_release") "m" Input.HeapScope.releaseBody mark releaseCode
  obtain ⟨positive,rest⟩ := Input.CallNormal.ignored_callee_return source middle (ofString "heap_release") [localVar "mark"] _
    Input.HeapScope.releaseBody callee .one args called released
  have actual := Input.HeapScope.release_call_execute source mark old [localVar "mark"] args heap releaseCode positive
  have middleEq := (congrArg Prod.snd (released.symm.trans actual))
  change middle=Input.HeapScope.releasePost {source with clock:=source.clock-1} mark at middleEq
  have postEq := (Input.return_normal middle post (localVar "r") returned tailRun).2
  rw [postEq,middleEq]
  simp [Input.HeapScope.releasePost,emptyLocalsHOLFinite,HolFiniteMapExact.update,FUPDATE]

/-- Normal original lookup suffix restores the saved mark, despite actual
hash writes/FFI events and nibble-buffer writes. No memory model is needed
for the restoration fact itself. -/
theorem after_alloc_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  -- Lookup arguments may fail; a normal whole suffix derives their actual
  -- argument values before the release continuation is reached.
  have safe : Input.LocalPrefix (ofString "mark") hash := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,hashRun,lookupRun,markEq⟩ := safe.normal_continue source post lookup returned normal
  have hashPure := Keccak256.globals (ofString "heap_ptr") source.code (Zero.original_code source.code installed)
    (GasBudget.Mcopy.copy_code source.code installed) (absorb_code source.code installed) (permutation_code source.code installed)
  have globalFrame := Input.GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "keccak256") hashArguments
    Keccak256.formals Keccak256.body .one (hash_original_code source.code installed) hashPure source rfl
  change Input.GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source hash).2=Input.GlobalEffects.erase (ofString "heap_ptr") source at globalFrame
  rw [hashRun] at globalFrame
  have middleHeap := (congrArg Prod.snd globalFrame).trans heap
  have middleInstalled := Input.OriginalCode.after_execution source middle hash none hashRun installed
  have middleMark := markEq.trans markCell
  obtain ⟨positive,actualValues,actualBody,callee,shape,target,answer,inner,args,called,bodyRun,checked,tailRun,restored⟩ :=
    Input.CallNormal.scoped_data middle post "r" TrieWalk.resultShape (ofString "trie_lookup") lookupArguments finish returned lookupRun
  have bodyEq := Input.GlobalEffects.lookup_body middle.code (ofString "trie_lookup") TrieLookup.formals TrieLookup.body TrieWalk.resultShape
    (TrieLookup.original_code middle.code middleInstalled) actualValues actualBody callee shape called
  subst actualBody
  have frame := TrieLookup.globals (ofString "heap_ptr") middle.code middleInstalled (callEntryStateHOLFinite middle callee) rfl
  rw [bodyRun] at frame
  let ready := Input.CallNormal.continuationEntry middle target "r" answer
  have readyMark : ready.locals.lookup (ofString "mark")=some (.val (.word mark)) :=
    (Input.CallNormal.continuation_lookup_other middle target "r" "mark" answer (by decide)).trans middleMark
  have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word old)) :=
    (congrArg Prod.snd frame).trans middleHeap
  have readyInstalled := Input.OriginalCode.after_execution (callEntryStateHOLFinite middle callee) target TrieLookup.body _ bodyRun middleInstalled
  have value := finish_heap ready inner mark old readyMark readyHeap readyInstalled returned tailRun
  rw [restored]
  exact value

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.finish_heap
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.after_alloc_heap
