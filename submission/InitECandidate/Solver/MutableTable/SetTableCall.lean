import InitECandidate.Solver.GasBudget.WarmKeysInvariant

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- The real setter transports its current owned table, including growth,
and derives its new heap cursor and amortized cost from the observed call. -/
theorem model_table_call (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (cursor floor : Nat)
    (table : TableState source kind plan slots cursor floor) (environment : GasBudget.WarmKeys.Environment source)
    (query value : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2^64)
    (queryMapped : ∀ offset < KeyHash.keySize kind,
      source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (TableCall.values (cell plan .header 0) query value))
    (run : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) = (none, target)) :
    ∃ paid nextPlan nextSlots nextCursor, paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      paid ≤ modelPrice kind plan.capacity slots.length + 1 ∧
      paid + GrowRuntime.growthPotential kind plan.capacity ≤
        noGrowthPrice kind slots.length + 1 + GrowRuntime.growthPotential kind nextPlan.capacity ∧
      TableState target kind nextPlan nextSlots nextCursor floor ∧ GasBudget.WarmKeys.Environment target ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      cell nextPlan .header 0 = cell plan .header 0 ∧ HeapGlobals source target ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite
        {source with globals := target.globals, memory := target.memory, clock := source.clock - paid} ∧
      target.locals = source.locals ∧
      (∀ address : BitVec 64, address.toNat < floor → target.memory address = source.memory address) := by
  obtain ⟨bits, power, minimum⟩ := table.power
  obtain ⟨paid, globals, memory, nextPlan, nextSlots, bounded, unchanged, funded, post, nextValid, nextHalf, sameLocals⟩ :=
    model_call_bound source target kind plan table.valid cursor table.bounded table.aligned table.earlier environment.domain environment.little
      slots table.half table.header table.occupied query value bits power minimum queryFits queryMapped table.heap
      environment.allocCode environment.trapCode environment.zeroCode environment.hashCode environment.copyCode environment.memeqCode
      environment.findCode environment.insertCode environment.growCode environment.setCode arguments args run
  have memoryEq := congrArg PanSemStateFiniteExact.memory post.frame
  have globalsEq := congrArg PanSemStateFiniteExact.globals post.frame
  have clock := congrArg PanSemStateFiniteExact.clock post.frame
  have codes := congrArg PanSemStateFiniteExact.code post.frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs post.frame
  have endian := congrArg PanSemStateFiniteExact.be post.frame
  change target.memory = memory at memoryEq
  change target.globals = globals at globalsEq
  change target.clock = source.clock - paid at clock
  change target.code = source.code at codes
  change target.memaddrs = source.memaddrs at domain
  change target.be = source.be at endian
  obtain ⟨nextBits, _, nextMinimum, nextPower⟩ := post.next_power table.valid bits power minimum
  obtain ⟨nextCursor, forward, cursorBound, cursorAligned, nextHeap, before⟩ :=
    post.cursor nextValid table.bounded table.aligned table.earlier table.heap
  have nextTable : TableState target kind nextPlan nextSlots nextCursor floor :=
    ⟨nextValid, nextHalf, by rw [memoryEq]; exact post.header, post.occupied, ⟨nextBits, nextPower, nextMinimum⟩,
      nextHeap, cursorBound, cursorAligned, before, post.pool_floor floor table.lower table.earlier⟩
  refine ⟨paid, nextPlan, nextSlots, nextCursor, funded, clock, bounded,
    post.amortized_power bits power minimum table.half bounded unchanged,
    nextTable, environment.of_fields codes domain endian, post.countBound.1, post.countBound.2,
    post.capacity_high_water, post.header_pointer, post.heap_globals, ?_, sameLocals, ?_⟩
  · rw [memoryEq, globalsEq]
    exact post.frame
  · intro address earlier
    exact post.protected_before nextValid floor table.lower table.earlier address earlier

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.model_table_call
