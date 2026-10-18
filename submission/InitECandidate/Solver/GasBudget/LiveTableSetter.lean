import InitECandidate.Solver.GasBudget.WarmKeysInvariant
import InitECandidate.Solver.MutableTable.SetModelSeparation

namespace InitECandidate.Solver.GasBudget.LiveTableSetter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

/-- Actual original setter while another table remains live. Growth derives
room and retains disjoint reader pools, its complete physical model and all
objects preceding the writer's lifetime floor. Both post-models share the
real returned cursor; array order may differ between individual pools. -/
theorem normal_bound (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind readerKind : KeyHash.Kind)
    (plan reader : Plan) (slots readerSlots : List Nat) (cursor floor readerFloor : Nat)
    (environment : WarmKeys.Environment source) (table : TableState source kind plan slots cursor floor)
    (readerTable : TableState source readerKind reader readerSlots cursor readerFloor)
    (apart : ∀ first second, plan.base first + size kind plan first ≤ reader.base second ∨ reader.base second + size readerKind reader second ≤ plan.base first)
    (query value : BitVec 64) (arguments : List (ExpHOL 64))
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableCall.values (cell plan .header 0) query value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) = (none, target)) :
    ∃ paid nextPlan nextSlots nextCursor,
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      paid + GrowRuntime.growthPotential kind plan.capacity ≤ Set.noGrowthPrice kind slots.length + 1 + GrowRuntime.growthPotential kind nextPlan.capacity ∧
      TableState target kind nextPlan nextSlots nextCursor floor ∧ TableState target readerKind reader readerSlots nextCursor readerFloor ∧
      (∀ first second, nextPlan.base first + size kind nextPlan first ≤ reader.base second ∨ reader.base second + size readerKind reader second ≤ nextPlan.base first) ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧ nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      cell nextPlan .header 0 = cell plan .header 0 ∧ target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧
      HeapGlobals source target ∧
      ∀ address : BitVec 64, address.toNat < floor → target.memory address = source.memory address := by
  obtain ⟨bits, power, minimum⟩ := table.power
  obtain ⟨paid, globals, memory, nextPlan, nextSlots, bounded, unchanged, fits, post, nextValid, nextHalf, sameLocals⟩ :=
    Set.model_call_bound source target kind plan table.valid cursor table.bounded table.aligned table.earlier environment.domain environment.little
      slots table.half table.header table.occupied query value bits power minimum queryFits queryMapped table.heap
      environment.allocCode environment.trapCode environment.zeroCode environment.hashCode environment.copyCode environment.memeqCode
      environment.findCode environment.insertCode environment.growCode environment.setCode arguments args normal
  have nextApart := post.reader_separate readerKind reader readerTable.earlier apart
  obtain ⟨readerHeader, readerModel⟩ := post.other_model nextValid readerKind reader readerTable.valid nextApart readerSlots readerTable.header readerTable.occupied
  obtain ⟨nextBits, _, nextMinimum, nextPower⟩ := post.next_power table.valid bits power minimum
  obtain ⟨nextCursor, forward, cursorBound, cursorAligned, nextHeap, before⟩ := post.cursor nextValid table.bounded table.aligned table.earlier table.heap
  have memoryEq := congrArg PanSemStateFiniteExact.memory post.frame
  change target.memory = memory at memoryEq
  have clockEq := congrArg PanSemStateFiniteExact.clock post.frame
  change target.clock = source.clock - paid at clockEq
  have codes := congrArg PanSemStateFiniteExact.code post.frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs post.frame
  have endian := congrArg PanSemStateFiniteExact.be post.frame
  change target.code = source.code at codes
  change target.memaddrs = source.memaddrs at domain
  change target.be = source.be at endian
  have nextTable : TableState target kind nextPlan nextSlots nextCursor floor :=
    ⟨nextValid, nextHalf, by rw [memoryEq]; exact post.header, post.occupied, ⟨nextBits, nextPower, nextMinimum⟩,
      nextHeap, cursorBound, cursorAligned, before, post.pool_floor floor table.lower table.earlier⟩
  have nextReader : TableState target readerKind reader readerSlots nextCursor readerFloor :=
    ⟨readerTable.valid, readerTable.half, readerHeader, readerModel, readerTable.power, nextHeap, cursorBound, cursorAligned,
      (by intro pool; have prior := readerTable.earlier pool; omega), readerTable.lower⟩
  exact ⟨paid, nextPlan, nextSlots, nextCursor, fits, clockEq, forward, post.amortized_power bits power minimum table.half bounded unchanged,
    nextTable, nextReader, nextApart, post.countBound.1, post.countBound.2, post.capacity_high_water, post.header_pointer, sameLocals, codes,
    environment.of_fields codes domain endian, post.heap_globals, fun address before => post.protected_before nextValid floor table.lower table.earlier address before⟩

end InitECandidate.Solver.GasBudget.LiveTableSetter

#print axioms InitECandidate.Solver.GasBudget.LiveTableSetter.normal_bound
