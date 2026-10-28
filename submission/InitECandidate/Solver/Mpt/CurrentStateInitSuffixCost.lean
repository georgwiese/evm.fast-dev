import InitECandidate.Solver.Mpt.StateInitProgram
import InitECandidate.Solver.Input.CurrentTable.NewCost
import InitECandidate.Solver.Input.ClockCostAssignedBody

namespace InitECandidate.Solver.Mpt.StateInit
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

private theorem store_suffix (code) (address value : ExpHOL 64) (tail : ProgHOL 64) (price : Nat)
    (back : ClockCost.Bound code tail price) : ClockCost.Bound code (.seq (.store address value) tail) price := by
  simpa only [Nat.zero_add] using ClockCost.sequence code _ _ 0 price (ClockCost.store code _ _) back

private theorem assign_suffix (code) (name : MlS) (value : ExpHOL 64) (tail : ProgHOL 64) (price : Nat)
    (back : ClockCost.Bound code tail price) : ClockCost.Bound code (.seq (.assign .global name value) tail) price := by
  simpa only [Nat.zero_add] using ClockCost.sequence code _ _ 0 price (ClockCost.of_quiet code _ (QuietClock.assign_kind code .global name value)) back

private theorem allocation_suffix (code) (installed : OriginalCode.Installed code)
    (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (price : Nat)
    (back : ClockCost.Bound code tail price) :
    ClockCost.Bound code (.seq (.call (some (destination,none)) (ofString "alloc") arguments) tail) (2+price) :=
  ClockCost.sequence code _ _ 2 price
    (ClockCost.assigned_body code destination (ofString "alloc") arguments PersistentAlloc.formals PersistentAlloc.body .one 1
      (PersistentAlloc.original_code code installed) (PersistentAlloc.body_price code installed)) back

private theorem table_suffix (code) (installed : OriginalCode.Installed code)
    (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (price : Nat)
    (back : ClockCost.Bound code tail price) :
    ClockCost.Bound code (.seq (.call (some (destination,none)) (ofString "htab_new") arguments) tail) (9+price) :=
  ClockCost.sequence code _ _ 9 price
    (ClockCost.assigned_body code destination (ofString "htab_new") arguments CurrentTable.New.formals CurrentTable.New.body .one 8
      (CurrentTable.New.original_code code installed) (CurrentTable.New.body_cost code installed)) back

set_option maxRecDepth 100000 in
/-- The literal current state suffix contains eight real Patricia table
constructors and three more allocations. Key sizes20/32/52 use their actual
constructor; no old hashmap implementation or successful allocation is assumed. -/
theorem current_after_root_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterRoot 78 := by
  simp only [afterRoot,rootCall,afterSecond,afterFirst,afterAllocation,body,Guest.Software.guestFn_state_init,
    progToHOL,shapeToHOL,Option.map_some,Option.map_none]
  apply store_suffix
  apply ClockCost.scoped_body (calleePrice:=8) (continuationPrice:=69) (formals:=CurrentTable.New.formals) (body:=CurrentTable.New.body) (returnShape:=.one)
  · exact CurrentTable.New.original_code code installed
  · exact CurrentTable.New.body_cost code installed
  · apply store_suffix
    apply allocation_suffix (price:=67) code installed
    apply store_suffix
    apply table_suffix (price:=58) code installed
    apply store_suffix
    apply table_suffix (price:=49) code installed
    apply store_suffix
    apply table_suffix (price:=40) code installed
    apply store_suffix
    apply table_suffix (price:=31) code installed
    apply store_suffix
    apply table_suffix (price:=22) code installed
    apply store_suffix
    apply table_suffix (price:=13) code installed
    apply store_suffix
    apply store_suffix
    apply store_suffix
    apply table_suffix (price:=4) code installed
    apply store_suffix
    apply allocation_suffix (price:=2) code installed
    apply assign_suffix
    apply allocation_suffix (price:=0) code installed
    apply assign_suffix
    apply assign_suffix
    exact ClockCost.returned code _

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.current_after_root_price
