import InitECandidate.Solver.WitnessRadix.AllocationEnvironment
import InitECandidate.Solver.Input.TrapCost
import InitECandidate.Solver.Input.ClockCostCurrentGuard
import InitECandidate.Solver.Input.ClockCostScoped

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "alloc")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 2 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_alloc) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.Software.guestFn_alloc,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem guard_price (code) (installed : Input.OriginalCode.Installed code) (test : ExpHOL 64)
    (continuation : ProgHOL 64) (tailPrice : Nat) (tail : Input.ClockCost.Bound code continuation tailPrice) :
    Input.ClockCost.Bound code (.seq (.ite test trap .skip) continuation) (max 1 tailPrice) := by
  intro source codeEq
  have currentInstalled : Input.OriginalCode.Installed source.code := by rw [codeEq]; exact installed
  have stops : (evaluateHOLFiniteState source trap).1≠none := by
    intro normal
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 1#64]=some (Input.Trap.values 1#64) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,Input.Trap.values]
    exact Input.Trap.call_not_normal source _ [.const 1#64] 1#64 (Input.Trap.original_code source.code currentInstalled) args (Prod.ext normal rfl)
  exact Input.ClockCost.stopping_guard_current source test trap continuation 1 tailPrice stops
    (Input.Trap.call_price code installed [.const 1#64] source codeEq) (tail source codeEq)

/-- Original persistent allocation costs at most one body source tick on
every outcome. Failed guards stop at trap_with, so two failures cannot add. -/
theorem body_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code body 1 := by
  have assigned : Input.ClockCost.Bound code assignment 0 :=
    Input.ClockCost.of_quiet code _ (Input.QuietClock.assign_kind code .global _ _)
  have final := Input.ClockCost.sequence code assignment returnPointer 0 0 assigned (Input.ClockCost.returned code _)
  have qPrice : Input.ClockCost.Bound code qTail 1 := guard_price code installed _ _ 0 final
  have declared := Input.ClockCost.declared code (ofString "q") .one roundExpression qTail 1 qPrice
  have pPrice : Input.ClockCost.Bound code pTail 1 := guard_price code installed _ _ 1 declared
  rw [body_shape]
  exact Input.ClockCost.declared code _ _ _ _ _ pPrice

theorem scoped_price (code) (installed : Input.OriginalCode.Installed code) (name : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (tail : Input.ClockCost.Bound code continuation tailPrice) :
    Input.ClockCost.Bound code (.decCall name shape (ofString "alloc") arguments continuation) (1+tailPrice+1) :=
  Input.ClockCost.scoped_body code name shape (ofString "alloc") arguments continuation formals body .one 1 tailPrice
    (original_code code installed) (body_price code installed) tail

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.original_code
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.guard_price
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.body_price
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.scoped_price
