import InitECandidate.Solver.Input.CurrentHash.AllocatorCost
import InitECandidate.Solver.Input.ClockCostTerminatingScoped
import InitECandidate.Solver.WitnessRadix.AllocationChecked

namespace InitECandidate.Solver.Input.CurrentHash.AllocationScopeCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Price a real scoped allocation on every observed non-timeout outcome.
Only its same normal return supplies the actual cursor, room and complete
nonlocal post-state to the continuation; failed allocations stop in the bound. -/
theorem cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor amount : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) (heapBound : cursor.toNat≤2952790016)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (PersistentAlloc.values amount))
    (tail : ∀ target : PanSemStateFiniteExact 64 Guest.HostMemory, cursor.toNat+amount.toNat≤2952790016 →
      LocalEffects.erase target=LocalEffects.erase (PersistentAlloc.post source cursor amount) → ∀ result final,
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word cursor))) continuation=(result,final) →
      result≠some .timeOut → target.clock-final.clock≤tailPrice)
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation)=(result,post))
    (notTimeout : result≠some .timeOut) : source.clock-post.clock≤tailPrice+2 := by
  obtain ⟨callee,called,amountLocal⟩ := PersistentAlloc.environment source.code.lookup amount (PersistentAlloc.original_code source.code installed)
  have composed := ClockCost.scoped_reached_terminating source post name .one (ofString "alloc") arguments (PersistentAlloc.values amount)
    PersistentAlloc.body continuation callee .one 1 tailPrice args called
    (by intro observed target evaluated notTimeout
        have priced := PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl
        rw [evaluated] at priced
        exact priced) (by
      intro target returned normal checked
      have room := PersistentAlloc.room_of_normal (callEntryStateHOLFinite source callee) target cursor amount amountLocal heap heapBound
        (Trap.original_code source.code installed) returned normal
      obtain ⟨valueEq,bound,aligned,frame⟩ := PersistentAlloc.checked_post_of_normal (callEntryStateHOLFinite source callee) target cursor amount amountLocal heap
        (Trap.original_code source.code installed) returned normal
      subst returned
      have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) frame
      change LocalEffects.erase target=LocalEffects.erase (PersistentAlloc.post source cursor amount) at same
      exact tail target room same) result actual notTimeout
  omega

end InitECandidate.Solver.Input.CurrentHash.AllocationScopeCost

#print axioms InitECandidate.Solver.Input.CurrentHash.AllocationScopeCost.cost
