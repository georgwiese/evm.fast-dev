import InitECandidate.Solver.Arenas.Normal
import InitECandidate.Solver.Input.TrapCost
import InitECandidate.Solver.Input.ClockCostCurrentGuard
import InitECandidate.Solver.Input.ClockCostScoped

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) (direction : Direction) :
    code.lookup (ofString (functionName direction))=some (formals,body direction,.one) := by
  cases direction with
  | up =>
    have checked := Input.OriginalCode.indexed code installed 5 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_frame_mem_alloc) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,functionName,
      Guest.guestFn_frame_mem_alloc,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  | down =>
    have checked := Input.OriginalCode.indexed code installed 8 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_scratch_alloc) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,functionName,
      Guest.guestFn_scratch_alloc,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem trap_guard_price (code) (installed : Input.OriginalCode.Installed code) (direction : Direction)
    (test : ExpHOL 64) (continuation : ProgHOL 64) (tailPrice : Nat)
    (tailCost : Input.ClockCost.Bound code continuation tailPrice) :
    Input.ClockCost.Bound code (.seq (.ite test (trap direction) .skip) continuation) (max 1 tailPrice) := by
  intro source codeEq
  have currentInstalled : Input.OriginalCode.Installed source.code := by rw [codeEq]; exact installed
  have firstCost := Input.Trap.call_price code installed [.const (trapCode direction)] source codeEq
  have stops : (evaluateHOLFiniteState source (trap direction)).1≠none := by
    intro normal
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const (trapCode direction)]=some (Input.Trap.values (trapCode direction)) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,Input.Trap.values]
    exact Input.Trap.call_not_normal source _ [.const (trapCode direction)] (trapCode direction) (Input.Trap.original_code source.code currentInstalled) args (Prod.ext normal rfl)
  exact Input.ClockCost.stopping_guard_current source test (trap direction) continuation 1 tailPrice stops firstCost (tailCost source codeEq)

/-- Both original allocator guards may trap, but a real trap cannot reach
the later guard. All actual body outcomes cost at most one source tick. -/
theorem body_price (code) (installed : Input.OriginalCode.Installed code) (direction : Direction) :
    Input.ClockCost.Bound code (body direction) 1 := by
  have assignPrice : Input.ClockCost.Bound code (assignment direction) 0 :=
    Input.ClockCost.of_quiet code _ (Input.QuietClock.assign_kind code .global _ _)
  have finalPrice := Input.ClockCost.sequence code (assignment direction) (.return (returnedExpression direction)) 0 0 assignPrice (Input.ClockCost.returned code _)
  have qPrice : Input.ClockCost.Bound code (qTail direction) 1 := trap_guard_price code installed direction _ _ 0 finalPrice
  have declaredPrice := Input.ClockCost.declared code (ofString "q") .one (roundExpression direction) (qTail direction) 1 qPrice
  have pPrice : Input.ClockCost.Bound code (pTail direction) 1 := trap_guard_price code installed direction _ _ 1 declaredPrice
  rw [body_shape]
  exact Input.ClockCost.declared code (ofString "p") .one (pointerExpression direction) (pTail direction) 1 pPrice

theorem call_price (code) (installed : Input.OriginalCode.Installed code) (direction : Direction)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call (Input.LocalEffects.callInfo destination) (ofString (functionName direction)) arguments) 2 :=
  Input.ClockCost.call_body code destination (ofString (functionName direction)) arguments formals (body direction) .one 1
    (original_code code installed direction) (body_price code installed direction)

theorem scoped_price (code) (installed : Input.OriginalCode.Installed code) (direction : Direction)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (tailCost : Input.ClockCost.Bound code continuation tailPrice) :
    Input.ClockCost.Bound code (.decCall name shape (ofString (functionName direction)) arguments continuation) (1+tailPrice+1) :=
  Input.ClockCost.scoped_body code name shape (ofString (functionName direction)) arguments continuation formals (body direction) .one 1 tailPrice
    (original_code code installed direction) (body_price code installed direction) tailCost

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.original_code
#print axioms InitECandidate.Solver.Arenas.trap_guard_price
#print axioms InitECandidate.Solver.Arenas.body_price
#print axioms InitECandidate.Solver.Arenas.call_price
#print axioms InitECandidate.Solver.Arenas.scoped_price
