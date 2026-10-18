import InitECandidate.Solver.GasBudget.WarmPrecompilesLocals
import InitECandidate.Solver.GasBudget.WarmKeysInvariant
import InitECandidate.Solver.MutableTable.SetModelNoGrowth

namespace InitECandidate.Solver.GasBudget.WarmPrecompiles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (start index cursor : Nat) (plan : Plan) (slots : List Nat)
    (inputValid : MemoryRegion.Valid ⟨start, 360⟩) (inside : index < 18)
    (environment : WarmKeys.Environment source) (valid : Valid .account plan) (capacity : plan.capacity = 64)
    (spare : slots.length ≤ 31) (earlier : ∀ pool, plan.base pool + size .account plan pool ≤ cursor)
    (cursorBound : cursor ≤ 33806089496) (cursorAligned : cursor % 8 = 0)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (header : MemoryModel.Header source.memory .account plan (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source .account plan slots)
    (locals : Locals source (cell plan .header 0) start index)
    (normal : evaluateHOLFiniteState source loopBody = (none, target)) :
    ∃ paid nextSlots, paid ≤ 9 * slots.length + 12 ∧ paid ≤ source.clock ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := source.clock - paid} ∧
      MemoryModel.Header target.memory .account plan (BitVec.ofNat 64 nextSlots.length) ∧ MemoryModel.Occupied target .account plan nextSlots ∧
      Locals target (cell plan .header 0) start (index + 1) ∧ slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧
      TableFootprint.Frame source.memory target.memory .account plan := by
  obtain ⟨called, setRun, incrementRun⟩ := Input.sequence_none source target setCall increment normal
  obtain ⟨queryFits, queryMapped⟩ := query_geometry source start index inputValid inside environment.domain
  obtain ⟨paid, globals, memory, nextPlan, nextSlots, bounded, unchanged, fits, post, nextValid, nextHalf, sameLocals⟩ :=
    Set.model_call_bound source called .account plan valid cursor cursorBound cursorAligned earlier environment.domain environment.little
      slots (by omega) header occupied (keyPointer start index) 1#64 6 capacity (by decide) queryFits queryMapped heap
      environment.allocCode environment.trapCode environment.zeroCode environment.hashCode environment.copyCode environment.memeqCode
      environment.findCode environment.insertCode environment.growCode environment.setCode _ (arguments_read source _ start index locals) setRun
  obtain ⟨samePlan, sameGlobals⟩ := post.no_growth valid.positive (by omega)
  subst nextPlan
  subst globals
  have calledGlobals := congrArg PanSemStateFiniteExact.globals post.frame
  change called.globals = source.globals at calledGlobals
  have memoryEq := congrArg PanSemStateFiniteExact.memory post.frame
  change called.memory = memory at memoryEq
  have calledLocals := locals.of_fields sameLocals calledGlobals
  have incrementActual := increment_execute called _ start index calledLocals
  have targetEq := congrArg Prod.snd (incrementRun.symm.trans incrementActual)
  change target = bind called "i" (BitVec.ofNat 64 (index + 1)) at targetEq
  subst target
  have linear := unchanged rfl
  rw [Set.no_growth_caller_price] at linear
  change paid ≤ 9 * slots.length + 12 at linear
  refine ⟨paid, nextSlots, linear, fits, ?_, ?_, ?_, calledLocals.next, post.countBound.1, post.countBound.2, ?_⟩
  · change emptyLocalsHOLFinite called = emptyLocalsHOLFinite {source with memory := called.memory, clock := source.clock - paid}
    rw [memoryEq]
    exact post.frame
  · change MemoryModel.Header called.memory .account plan (BitVec.ofNat 64 nextSlots.length)
    rw [memoryEq]
    exact post.header
  · exact MemoryModel.Occupied.of_fields called _ .account plan nextSlots post.occupied rfl rfl rfl
  · change TableFootprint.Frame source.memory called.memory .account plan
    rw [memoryEq]
    exact post.footprint

end InitECandidate.Solver.GasBudget.WarmPrecompiles

#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.body_normal
