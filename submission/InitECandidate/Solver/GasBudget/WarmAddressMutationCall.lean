import InitECandidate.Solver.GasBudget.WarmAddressMutation
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.GasBudget.WarmAddressMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame query : BitVec 64)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (expressions : List (ExpHOL 64))
    (expectedArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word query)])
    (run : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "warm_address") expressions) = (none, post)) :
    ∃ paid nextPlan nextSlots nextCursor, paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account plan.capacity ≤ 9 * slots.length + 13 + GrowRuntime.growthPotential .account nextPlan.capacity ∧
      TableState post .account nextPlan nextSlots nextCursor floor ∧ WarmKeys.Environment post ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      cell nextPlan .header 0 = cell plan .header 0 ∧ HeapGlobals source post ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite
        {source with globals := post.globals, memory := post.memory, clock := source.clock - paid} ∧
      (∀ address : BitVec 64, address.toNat < floor → post.memory address = source.memory address) ∧ post.locals = source.locals := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, callerFields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "warm_address") expressions run
  obtain ⟨argument, valuesEq, bodyEq, shapeEq, typed, binding⟩ := Input.CallNormal.unary_lookup_data source.code.lookup
    (ofString "warm_address") (ofString "addr") .one body .one (original_code source.code installed)
    values actual callee shape called
  rw [valuesEq] at args
  have argumentEq : argument = .val (.word query) := by
    have same := Option.some.inj (args.symm.trans expectedArgs)
    simpa using same
  rw [argumentEq] at binding
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨zero, paid, nextPlan, nextSlots, nextCursor, funded, clock, amortized, nextTable, nextEnvironment,
    countLower, countUpper, capacity, header, globals, fields, outside⟩ :=
    body_normal entry target frame query plan slots cursor floor (table.of_fields rfl rfl rfl rfl)
      (environment.of_fields rfl rfl rfl) ev tableMapped tableCell binding queryFits queryMapped returned bodyRun
  change paid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - paid at clock
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  have targetClock : target.clock = source.clock - (paid + 1) := clock.trans subtract
  refine ⟨paid + 1, nextPlan, nextSlots, nextCursor, by omega, by rw [postEq]; exact targetClock,
    by omega, nextTable.of_fields (by rw [postEq]) (by rw [postEq]) (by rw [postEq]) (by rw [postEq]),
    nextEnvironment.of_fields (by rw [postEq]) (by rw [postEq]) (by rw [postEq]),
    countLower, countUpper, capacity, header, ?_, ?_, ?_, by rw [postEq]⟩
  · intro key different
    rw [postEq]
    exact globals key different
  · rw [postEq]
    have canonical : emptyLocalsHOLFinite target = emptyLocalsHOLFinite
        {source with globals := target.globals, memory := target.memory, clock := source.clock - 1 - paid} := fields
    rw [subtract] at canonical
    exact canonical
  · intro address earlier
    rw [postEq]
    exact outside address earlier

end InitECandidate.Solver.GasBudget.WarmAddressMutation

#print axioms InitECandidate.Solver.GasBudget.WarmAddressMutation.call_normal
