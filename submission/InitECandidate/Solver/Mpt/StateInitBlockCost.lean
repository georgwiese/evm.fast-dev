import InitECandidate.Solver.Mpt.StateInitBlockProgram
import InitECandidate.Solver.Mpt.StateInitTailNormal
import InitECandidate.Solver.MutableTable.TableRuntime.CallCost

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString GasBudget.Journal WitnessRadix.QueryBranch

def constructorPrice : List Action→Nat
  | []=>0
  | .table _ bits _::rest=>TableRuntime.costPrice (2^bits)+constructorPrice rest
  | .scalar ..::rest=>constructorPrice rest

theorem program_cost (specs : List Action) (code) (tail : ProgHOL 64) (tailPrice : Nat)
    (installed : Input.OriginalCode.Installed code) (valid : ∀ action∈specs,action.Valid)
    (back : Input.ClockCost.Bound code tail tailPrice) :
    Input.ClockCost.Bound code (program specs tail) (constructorPrice specs+tailPrice):=by
  induction specs with
  | nil=>simpa only [program,constructorPrice,Nat.zero_add] using back
  | cons action rest ih=>
    have next:=ih (fun later member=>valid later (List.mem_cons_of_mem _ member))
    cases action with
    | scalar offset value=>
      have stored : Input.ClockCost.Bound code (fieldStore offset (.const value)) 0:=Input.ClockCost.store code _ _
      simpa only [program,constructorPrice,Nat.zero_add] using Input.ClockCost.sequence code _ _ 0 _ stored next
    | table kind bits offset=>
      have current:=valid (.table kind bits offset) List.mem_cons_self
      have capBound : 2^bits≤256:=Nat.pow_le_pow_right (by decide) current.2.1
      have front : Input.ClockCost.Bound code (tableCall kind bits) (TableRuntime.costPrice (2^bits)):=by
        intro source codeEq
        have sourceInstalled : Input.OriginalCode.Installed source.code:=by rewrite [codeEq]; exact installed
        exact TableRuntime.assigned_cost source kind (2^bits) (some (.local,ofString "t")) (tableArguments kind bits) (by omega) sourceInstalled rfl
      have field : Input.ClockCost.Bound code (fieldStore offset (localVar "t")) 0:=Input.ClockCost.store code _ _
      have stored:=Input.ClockCost.sequence code _ _ 0 _ field next
      have whole:=Input.ClockCost.sequence code _ _ (TableRuntime.costPrice (2^bits)) (0+(constructorPrice rest+tailPrice)) front stored
      simpa only [program,constructorPrice,Nat.zero_add,Nat.add_assoc] using whole

theorem constructor_price_all : constructorPrice actions=1656:=by decide

theorem allocation_bound (code) (installed : Input.OriginalCode.Installed code) (name : String) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call (some (some (.global,ofString name),none)) (ofString "alloc") arguments) 2:=
  Input.ClockCost.assigned_body code (some (.global,ofString name)) (ofString "alloc") arguments PersistentAlloc.formals PersistentAlloc.body .one 1
    (PersistentAlloc.original_code code installed) (PersistentAlloc.body_price code installed)

theorem journal_bound (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code Initialization.selected 2:=by
  rw [Initialization.actual_site]
  have assigned (name : MlS) (value : ExpHOL 64) : Input.ClockCost.Bound code (.assign .global name value) 0:=
    Input.ClockCost.of_quiet code _ (Input.QuietClock.assign_kind code .global name value)
  have reset:=Input.ClockCost.sequence code Initialization.resetTransaction (.return (.const 0#64)) 0 0 (assigned _ _) (Input.ClockCost.returned code _)
  have counted:=Input.ClockCost.sequence code Initialization.resetCounter _ 0 0 (assigned _ _) reset
  have allocated:=Input.ClockCost.sequence code Initialization.allocate Initialization.afterAllocation 2 0
    (allocation_bound code installed "journal" Initialization.allocationArguments) counted
  exact Input.ClockCost.sequence code Initialization.setCap _ 0 2 (assigned _ _) allocated

theorem tail_bound (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterFields 4:=by
  rw [tail_shape]
  exact Input.ClockCost.sequence code allocateScratch Initialization.selected 2 2 (allocation_bound code installed "sk_buf" [.const 64#64]) (journal_bound code installed)

set_option maxRecDepth 100000 in
/-- Every outcome of the complete actual block suffix costs at most1662
source clocks. No physical state, room or successful constructor is assumed. -/
theorem body_cost (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterStorageTrie 1662:=by
  rw [shapes.1]
  have fields : Input.ClockCost.Bound code afterWorkspace (1656+4):=by
    rw [shapes.2.2]
    have price:=program_cost actions code afterFields 4 installed actions_valid (tail_bound code installed)
    simpa only [constructor_price_all] using price
  have stored:=Input.ClockCost.sequence code storeWorkspace afterWorkspace 0 (1656+4) (Input.ClockCost.store code _ _) fields
  rw [shapes.2.1]
  exact Input.ClockCost.sequence code allocate _ 2 (0+(1656+4)) (allocation_bound code installed "bs" [.const 80#64]) stored

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.program_cost
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.constructor_price_all
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.allocation_bound
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.journal_bound
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.tail_bound
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.body_cost
