import InitECandidate.Solver.MutableTable.SetTableCall
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.GasBudget.WarmAddressMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

def body : ProgHOL 64 := match Guest.guestFn_warm_address with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr", .one)]
def arguments : List (ExpHOL 64) := [frameLoad 168#64, localVar "addr", .const 1#64]
def setCall : ProgHOL 64 := .call (some (none, none)) (ofString "htab_set") arguments

theorem body_shape : body = .seq setCall (.return (.const 0#64)) := by
  simp only [body, Guest.guestFn_warm_address, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    setCall, arguments, localVar, frameLoad, frameAddress, Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "warm_address") = some (formals, body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 430 (OriginalCodeEnvironment.originalEntry Guest.guestFn_warm_address) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals,
    Guest.guestFn_warm_address, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame query : BitVec 64)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧
    ∃ paid nextPlan nextSlots nextCursor, paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account plan.capacity ≤ 9 * slots.length + 12 + GrowRuntime.growthPotential .account nextPlan.capacity ∧
      TableState post .account nextPlan nextSlots nextCursor floor ∧ WarmKeys.Environment post ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      cell nextPlan .header 0 = cell plan .header 0 ∧ HeapGlobals source post ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite
        {source with globals := post.globals, memory := post.memory, clock := source.clock - paid} ∧
      (∀ address : BitVec 64, address.toNat < floor → post.memory address = source.memory address) := by
  have tableRead := frame_read source frame 168#64 (cell plan .header 0) ev tableMapped tableCell
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (TableCall.values (cell plan .header 0) query 1#64) := by
    simp only [eval] at tableRead
    simp [arguments, TableCall.values, evalListHOLFinite, evalListHOLExact, tableRead, evalHOLExact, toExact, localVar, queryLocal]
  rw [body_shape] at run
  have safe : Input.LocalPrefix (ofString "addr") setCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨called, setRun, returnRun, saved⟩ := safe.normal_continue source post (.return (.const 0#64)) returned run
  obtain ⟨paid, nextPlan, nextSlots, nextCursor, funded, clock, bounded, amortized, nextTable, nextEnvironment,
    countLower, countUpper, capacity, header, globals, fields, locals, outside⟩ :=
    Set.model_table_call source called .account plan slots cursor floor table environment query 1#64 queryFits queryMapped arguments args setRun
  obtain ⟨read, postEq⟩ := Input.return_normal called post (.const 0#64) returned returnRun
  have zero : returned = .val (.word 0#64) := by
    have expected : eval called (.const 0#64) = some (.val (.word 0#64)) := rfl
    exact Option.some.inj (read.symm.trans expected)
  rw [Set.no_growth_caller_price] at amortized
  refine ⟨zero, paid, nextPlan, nextSlots, nextCursor, funded, by rw [postEq]; exact clock, amortized,
    nextTable.of_fields (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl),
    nextEnvironment.of_fields (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl),
    countLower, countUpper, capacity, header, ?_, ?_, ?_⟩
  · intro key different
    rw [postEq]
    exact globals key different
  · rw [postEq]
    exact fields
  · intro address earlier
    rw [postEq]
    exact outside address earlier

end InitECandidate.Solver.GasBudget.WarmAddressMutation

#print axioms InitECandidate.Solver.GasBudget.WarmAddressMutation.body_shape
#print axioms InitECandidate.Solver.GasBudget.WarmAddressMutation.original_code
#print axioms InitECandidate.Solver.GasBudget.WarmAddressMutation.body_normal
