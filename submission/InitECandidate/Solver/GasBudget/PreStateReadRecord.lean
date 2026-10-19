import InitECandidate.Solver.MutableTable.FamilySet
import InitECandidate.Solver.MutableTable.FamilyFloorFrame
import InitECandidate.Solver.MutableTable.FamilyControl
import InitECandidate.Solver.Input.GlobalFieldRead
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.GasBudget.PreStateReadRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

def body : ProgHOL 64 := match Guest.guestFn_record_pre_state_read with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr", .one)]
def arguments : List (ExpHOL 64) := [.load .one (addConst (.var .global (ofString "bs")) 72#64), localVar "addr", .const 1#64]
def setCall : ProgHOL 64 := .call (some (none, none)) (ofString "htab_set") arguments

theorem body_shape : body = .seq setCall (.return (.const 0#64)) := by
  simp only [body, Guest.guestFn_record_pre_state_read, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    setCall, arguments, localVar, addConst, Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "record_pre_state_read") = some (formals, body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 332 (OriginalCodeEnvironment.originalEntry Guest.guestFn_record_pre_state_read) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals,
    Guest.guestFn_record_pre_state_read, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

/-- Actual recording of a pre-state account read transports the entire live
table family through its possible insertion/growth. No future family is supplied. -/
theorem body_normal {ι : Type} [DecidableEq ι] (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block query : BitVec 64) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (family : TableFamily.Model source cursor objects) (kind : (objects writer).kind = .account)
    (environment : WarmKeys.Environment source)
    (blockGlobal : source.globals.lookup (ofString "bs") = some (.val (.word block)))
    (mapped : source.memaddrs (block + 72#64)) (stored : source.memory (block + 72#64) = .word (objects writer).pointer)
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      next.kind = .account ∧ TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      paid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 12 + GrowRuntime.growthPotential .account next.plan.capacity ∧
      (objects writer).slots.length ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length + 1 ∧
      next.plan.capacity ≤ max (objects writer).plan.capacity (4 * (next.slots.length + 1)) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ HeapGlobals source post ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source post := by
  classical
  have tableRead := Input.global_field_read source "bs" block 72#64 (objects writer).pointer blockGlobal mapped stored
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (TableCall.values (objects writer).pointer query 1#64) := by
    simp only [eval] at tableRead
    change evalListHOLExact source.toExact arguments = _
    rw [arguments, evalListHOLExact, tableRead]
    simp [TableCall.values, evalListHOLExact, evalHOLExact, toExact, localVar, queryLocal]
  rw [body_shape] at run
  have safe : Input.LocalPrefix (ofString "addr") setCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨called, setRun, returnRun, saved⟩ := safe.normal_continue source post (.return (.const 0#64)) returned run
  obtain ⟨paid, nextCursor, next, funded, clock, forward, nextKind, nextFloor, nextFamily, pointers, amortized,
    countLower, countUpper, capacity, locals, codes, nextEnvironment, globals, protectedWords, earlier⟩ :=
    TableFamily.set_normal source called cursor objects writer family environment query 1#64 arguments
      (by rw [kind]; exact queryFits) (by rw [kind]; exact queryMapped) args setRun
  obtain ⟨read, postEq⟩ := Input.return_normal called post (.const 0#64) returned returnRun
  have zero : returned = .val (.word 0#64) := Option.some.inj (read.symm.trans rfl)
  rw [kind, Set.no_growth_caller_price] at amortized
  have postFamily : TableFamily.Model post nextCursor (Function.update objects writer next) :=
    nextFamily.of_control (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl)
  refine ⟨zero, paid, nextCursor, next, funded, by rw [postEq]; exact clock, forward, nextKind.trans kind,
    postFamily, pointers, amortized, countLower, countUpper, capacity, by rw [postEq]; exact codes,
    nextEnvironment.of_fields (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl), ?_, ?_⟩
  · intro key different
    rw [postEq]
    exact globals key different
  · apply TableFamily.FloorFrame.of_update objects writer next source post nextFloor
    intro address before
    rw [postEq]
    exact protectedWords address before

end InitECandidate.Solver.GasBudget.PreStateReadRecord

#print axioms InitECandidate.Solver.GasBudget.PreStateReadRecord.body_shape
#print axioms InitECandidate.Solver.GasBudget.PreStateReadRecord.original_code
#print axioms InitECandidate.Solver.GasBudget.PreStateReadRecord.body_normal
