import InitECandidate.Solver.GasBudget.WarmKeysInvariant

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- One real storage-key warming body, obtained from its normal execution.
The physical table, allocation cursor and protected earlier objects all
survive; growth contributes only its increase in amortized potential. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start total index floor cursor : Nat) (plan : Plan) (slots : List Nat)
    (inputValid : MemoryRegion.Valid (inputRegion start total)) (inside : index < total)
    (environment : Environment source) (table : Table source plan slots cursor floor)
    (locals : Locals source (cell plan .header 0) start total index)
    (normal : evaluateHOLFiniteState source loopBody = (none, target)) :
    ∃ paid nextPlan nextSlots nextCursor,
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .storage plan.capacity ≤ 13 * slots.length + 16 + GrowRuntime.growthPotential .storage nextPlan.capacity ∧
      Table target nextPlan nextSlots nextCursor floor ∧ Environment target ∧
      Locals target (cell nextPlan .header 0) start total (index + 1) ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      HeapGlobals source target ∧
      ∀ address : BitVec 64, address.toNat < floor → target.memory address = source.memory address := by
  obtain ⟨called, setRun, incrementRun⟩ := Input.sequence_none source target setCall increment normal
  obtain ⟨bits, power, minimum⟩ := table.power
  obtain ⟨queryFits, queryMapped⟩ := query_geometry source start total index inputValid inside environment.domain
  obtain ⟨paid, globals, memory, nextPlan, nextSlots, bounded, unchanged, fits, post, nextValid, nextHalf, sameLocals⟩ :=
    Set.model_call_bound source called .storage plan table.valid cursor table.bounded table.aligned table.earlier environment.domain environment.little
      slots table.half table.header table.occupied (keyPointer start index) 1#64 bits power minimum queryFits queryMapped table.heap
      environment.allocCode environment.trapCode environment.zeroCode environment.hashCode environment.copyCode environment.memeqCode
      environment.findCode environment.insertCode environment.growCode environment.setCode _ (arguments_read source _ start total index locals) setRun
  have calledLocals := locals.of_locals sameLocals
  have incrementActual := increment_execute called _ start total index calledLocals
  have targetEq := congrArg Prod.snd (incrementRun.symm.trans incrementActual)
  change target = bind called "i" (BitVec.ofNat 64 (index + 1)) at targetEq
  subst target
  have memoryEq := congrArg PanSemStateFiniteExact.memory post.frame
  change called.memory = memory at memoryEq
  have clockEq := congrArg PanSemStateFiniteExact.clock post.frame
  change called.clock = source.clock - paid at clockEq
  have codes := congrArg PanSemStateFiniteExact.code post.frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs post.frame
  have endian := congrArg PanSemStateFiniteExact.be post.frame
  change called.code = source.code at codes
  change called.memaddrs = source.memaddrs at domain
  change called.be = source.be at endian
  have calledEnvironment : Environment called := environment.of_fields codes domain endian
  obtain ⟨nextBits, _, nextMinimum, nextPower⟩ := post.next_power table.valid bits power minimum
  obtain ⟨nextCursor, forward, cursorBound, cursorAligned, nextHeap, before⟩ := post.cursor nextValid table.bounded table.aligned table.earlier table.heap
  have calledTable : Table called nextPlan nextSlots nextCursor floor :=
    ⟨nextValid, nextHalf, by rw [memoryEq]; exact post.header, post.occupied, ⟨nextBits, nextPower, nextMinimum⟩,
      nextHeap, cursorBound, cursorAligned, before, post.pool_floor floor table.lower table.earlier⟩
  have nextTable := calledTable.of_fields (target := bind called "i" (BitVec.ofNat 64 (index + 1))) rfl rfl rfl rfl
  have amortized := post.amortized_power bits power minimum table.half bounded unchanged
  have linear : Set.noGrowthPrice .storage slots.length + 1 = 13 * slots.length + 16 := Set.no_growth_caller_price .storage slots.length
  rw [linear] at amortized
  refine ⟨paid, nextPlan, nextSlots, nextCursor, fits, clockEq, amortized, nextTable,
    calledEnvironment.of_fields rfl rfl rfl, ?_, post.countBound.1, post.countBound.2, post.capacity_high_water, post.heap_globals, ?_⟩
  · rw [post.header_pointer]
    exact calledLocals.next
  · intro address earlier
    exact post.protected_before nextValid floor table.lower table.earlier address earlier

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.body_normal
