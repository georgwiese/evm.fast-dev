import InitECandidate.Solver.GasBudget.WarmAddressesLocals
import InitECandidate.Solver.GasBudget.WarmKeysInvariant

namespace InitECandidate.Solver.GasBudget.WarmAddresses
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- One real access-list address warming body, obtained from its normal execution.
The physical table, allocation cursor and protected earlier objects all
survive; growth contributes only its increase in amortized potential. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start count index floor cursor : Nat) (plan : Plan) (slots : List Nat) (pointers : Nat → BitVec 64)
    (array : PointerArray source.memory 20 start count floor pointers) (inside : index < count)
    (environment : WarmKeys.Environment source) (table : TableState source .account plan slots cursor floor)
    (locals : Locals source (cell plan .header 0) start count index)
    (normal : evaluateHOLFiniteState source loopBody = (none, target)) :
    ∃ paid nextPlan nextSlots nextCursor,
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account plan.capacity ≤ 9 * slots.length + 12 + GrowRuntime.growthPotential .account nextPlan.capacity ∧
      TableState target .account nextPlan nextSlots nextCursor floor ∧ WarmKeys.Environment target ∧
      PointerArray target.memory 20 start count floor pointers ∧
      Locals target (cell nextPlan .header 0) start count (index + 1) ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      ∀ address : BitVec 64, address.toNat < floor → target.memory address = source.memory address := by
  obtain ⟨called, setRun, incrementRun⟩ := Input.sequence_none source target setCall increment normal
  obtain ⟨bits, power, minimum⟩ := table.power
  have queryFits := array.fits index inside
  have queryMapped : ∀ offset < KeyHash.keySize .account, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress (pointers index) offset)) := by
    intro offset small
    rw [environment.domain]
    exact array.mapped index inside offset small
  obtain ⟨paid, globals, memory, nextPlan, nextSlots, bounded, unchanged, fits, post, nextValid, nextHalf, sameLocals⟩ :=
    Set.model_call_bound source called .account plan table.valid cursor table.bounded table.aligned table.earlier environment.domain environment.little
      slots table.half table.header table.occupied (pointers index) 1#64 bits power minimum queryFits queryMapped table.heap
      environment.allocCode environment.trapCode environment.zeroCode environment.hashCode environment.copyCode environment.memeqCode
      environment.findCode environment.insertCode environment.growCode environment.setCode _ (arguments_read source _ start count index floor pointers array inside environment.domain locals) setRun
  have calledLocals := locals.of_locals sameLocals
  have incrementActual := increment_execute called _ start count index calledLocals
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
  have calledEnvironment : WarmKeys.Environment called := environment.of_fields codes domain endian
  obtain ⟨nextBits, _, nextMinimum, nextPower⟩ := post.next_power table.valid bits power minimum
  obtain ⟨nextCursor, forward, cursorBound, cursorAligned, nextHeap, before⟩ := post.cursor nextValid table.bounded table.aligned table.earlier table.heap
  have calledTable : TableState called .account nextPlan nextSlots nextCursor floor :=
    ⟨nextValid, nextHalf, by rw [memoryEq]; exact post.header, post.occupied, ⟨nextBits, nextPower, nextMinimum⟩,
      nextHeap, cursorBound, cursorAligned, before, post.pool_floor floor table.lower table.earlier⟩
  have nextTable := calledTable.of_fields (target := bind called "i" (BitVec.ofNat 64 (index + 1))) rfl rfl rfl rfl
  have amortized := post.amortized_power bits power minimum table.half bounded unchanged
  have linear : Set.noGrowthPrice .account slots.length + 1 = 9 * slots.length + 12 := Set.no_growth_caller_price .account slots.length
  rw [linear] at amortized
  refine ⟨paid, nextPlan, nextSlots, nextCursor, fits, clockEq, amortized, nextTable,
    calledEnvironment.of_fields rfl rfl rfl, ?_, ?_, post.countBound.1, post.countBound.2, post.capacity_high_water, ?_⟩
  · exact array.of_protected (fun address earlier => post.protected_before nextValid floor table.lower table.earlier address earlier)
  · rw [post.header_pointer]
    exact calledLocals.next
  · intro address earlier
    exact post.protected_before nextValid floor table.lower table.earlier address earlier

end InitECandidate.Solver.GasBudget.WarmAddresses

#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.body_normal
