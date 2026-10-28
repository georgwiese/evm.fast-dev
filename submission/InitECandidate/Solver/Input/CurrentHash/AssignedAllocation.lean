import InitECandidate.Solver.Input.CurrentHash.AllocationScopeCost
import InitECandidate.Solver.Input.AssignedCallKnown

namespace InitECandidate.Solver.Input.CurrentHash.AssignedAllocation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real allocator assigning an existing local derives the actual returned
cursor, allocation room, caller binding and complete nonlocal post-state.
This uses the current persistent ceiling, including the actual trap path. -/
theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor amount : BitVec 64)
    (installed : OriginalCode.Installed source.code) (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (heapBound : cursor.toNat≤2952790016) (name : String) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (PersistentAlloc.values amount))
    (actual : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "alloc") arguments)=(none,target)) :
    cursor.toNat+amount.toNat≤2952790016 ∧ target.locals.lookup (ofString name)=some (.val (.word cursor)) ∧
      (∀ other,ofString name≠other → target.locals.lookup other=source.locals.lookup other) ∧
      LocalEffects.erase target=LocalEffects.erase (PersistentAlloc.post source cursor amount) := by
  obtain ⟨callee,called,amountLocal⟩ := PersistentAlloc.environment source.code.lookup amount (PersistentAlloc.original_code source.code installed)
  obtain ⟨funded,childTarget,returned,bodyRun,endpoint⟩ := CallNormal.local_known source target (ofString name) (ofString "alloc") arguments
    (PersistentAlloc.values amount) PersistentAlloc.body callee .one args called actual
  let entry := callEntryStateHOLFinite source callee
  have room := PersistentAlloc.room_of_normal entry childTarget cursor amount amountLocal heap heapBound (Trap.original_code source.code installed) returned bodyRun
  obtain ⟨valueEq,nextBound,nextAligned,frame⟩ := PersistentAlloc.checked_post_of_normal entry childTarget cursor amount amountLocal heap
    (Trap.original_code source.code installed) returned bodyRun
  subst returned
  have frozen := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) frame
  change LocalEffects.erase childTarget=LocalEffects.erase (PersistentAlloc.post source cursor amount) at frozen
  refine ⟨room,?_,?_,?_⟩
  · rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro other different
    rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
  · rw [endpoint]
    exact frozen

end InitECandidate.Solver.Input.CurrentHash.AssignedAllocation

#print axioms InitECandidate.Solver.Input.CurrentHash.AssignedAllocation.normal
