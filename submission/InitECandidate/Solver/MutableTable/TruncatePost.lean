import InitECandidate.Solver.MutableTable.TruncateStop

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

structure ModelPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (initialCount : Nat)
    (limit : BitVec 64) (paid : Nat) (memory : WordWrites.Memory) (target : PanSemStateFiniteExact 64 Guest.HostMemory) (next : List Nat) : Prop where
  frame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid}
  length : next.length = min initialCount limit.toNat
  header : MemoryModel.Header memory kind plan (BitVec.ofNat 64 next.length)
  occupied : MemoryModel.Occupied target kind plan next
  footprint : TableFootprint.Frame source.memory memory kind plan

theorem stopped_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (slots : List Nat) (room : slots.length < plan.capacity)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind plan slots)
    (limit : BitVec 64) (stopped : slots.length ≤ limit.toNat)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (limitLocal : source.locals.lookup (ofString "n") = some (.val (.word limit)))
    (normal : evaluateHOLFiniteState source tail = (some (.returned (.val (.word 0#64))), target)) :
    ModelPost source kind plan slots.length limit 0 source.memory target slots := by
  have actual := stop_execute source kind plan valid domain slots.length room header limit stopped tableLocal limitLocal
  have targetEq := congrArg Prod.snd (normal.symm.trans actual)
  change target = emptyLocalsHOLFinite source at targetEq
  subst target
  exact ⟨by simp only [Nat.sub_zero, emptyLocalsHOLFinite], (Nat.min_eq_left stopped).symm, header,
    MemoryModel.Occupied.of_fields source _ kind plan slots occupied rfl rfl rfl, TableFootprint.Frame.refl _ _ _⟩


theorem stopped_post_result (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (slots : List Nat) (room : slots.length < plan.capacity)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind plan slots)
    (limit : BitVec 64) (stopped : slots.length ≤ limit.toNat)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (limitLocal : source.locals.lookup (ofString "n") = some (.val (.word limit))) (result : Option (PanSemResultExact 64))
    (normal : evaluateHOLFiniteState source tail = (result, target)) :
    result = some (.returned (.val (.word 0#64))) ∧ ModelPost source kind plan slots.length limit 0 source.memory target slots := by
  have actual := stop_execute source kind plan valid domain slots.length room header limit stopped tableLocal limitLocal
  have resultEq := congrArg Prod.fst (normal.symm.trans actual)
  change result = some (.returned (.val (.word 0#64))) at resultEq
  refine ⟨resultEq, stopped_post source target kind plan valid domain slots room header occupied limit stopped tableLocal limitLocal ?_⟩
  simpa only [resultEq] using normal

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.stopped_post

#print axioms InitECandidate.Solver.MutableTable.Truncate.stopped_post_result
