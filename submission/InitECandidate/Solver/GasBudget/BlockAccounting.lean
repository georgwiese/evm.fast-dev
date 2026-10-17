import InitECandidate.Solver.GasBudget.StorageClassify

namespace InitECandidate.Solver.GasBudget.BlockAccounting
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def regularCost (gas liquid stateLeft stateUsed floor : Nat) : Nat:=max (gas-liquid-stateLeft-stateUsed) floor

/-- Conditional natural accounting, before ordinary refund. Nonnegative state
use and the gas-pool equation must come from the actual state/frame invariant. -/
theorem regular_cost (gas liquid used stateLeft stateUsed intrinsic floor : Nat)
    (pools : gas=intrinsic+liquid+used+stateLeft+stateUsed) :
    regularCost gas liquid stateLeft stateUsed floor=max (intrinsic+used) floor := by
  unfold regularCost
  congr 1
  omega

theorem regular_bounds (gas liquid used stateLeft stateUsed intrinsic floor : Nat)
    (pools : gas=intrinsic+liquid+used+stateLeft+stateUsed)
    (usedBound : intrinsic+used≤min 16777216 gas) (floorBound : floor≤min 16777216 gas) :
    intrinsic+used≤regularCost gas liquid stateLeft stateUsed floor ∧
      regularCost gas liquid stateLeft stateUsed floor≤min 16777216 gas := by
  rw [regular_cost _ _ _ _ _ _ _ pools]
  exact ⟨Nat.le_max_left _ _,max_le usedBound floorBound⟩

/-- A passed reservation check bounds both the completed update and an
unfinished final transaction's work. No sum of declared root budgets is used. -/
theorem reservation (limit before gas cost work : Nat) (prior : before≤limit)
    (checked : min 16777216 gas≤limit-before) (costBound : cost≤min 16777216 gas)
    (workBound : work≤cost) : before+cost≤limit ∧ before+work≤limit := by omega

structure Entry where
  work : Nat
  cost : Nat
  paid : work≤cost

def costs (entries : List Entry) : Nat:=(entries.map Entry.cost).sum
def works (entries : List Entry) : Nat:=(entries.map Entry.work).sum

theorem work_le_cost (entries : List Entry) : works entries≤costs entries := by
  induction entries with
  | nil=>simp [works,costs]
  | cons entry rest ih=>
    have paid:=entry.paid
    simp only [works,costs,List.map_cons,List.sum_cons] at ih ⊢
    omega

/-- Include a last transaction that failed before committing its block gas
counter, using its already passed reservation check. -/
theorem aggregate_with_partial (entries : List Entry) (limit lastGas lastWork : Nat)
    (prior : costs entries≤limit) (checked : min 16777216 lastGas≤limit-costs entries)
    (lastBound : lastWork≤min 16777216 lastGas) : works entries+lastWork≤limit := by
  have paid:=work_le_cost entries
  omega

theorem completed_count (entries : List Entry) (minimumCost : Nat)
    (positive : ∀ entry∈entries,minimumCost≤entry.cost) : entries.length*minimumCost≤costs entries := by
  induction entries with
  | nil=>simp [costs]
  | cons entry rest ih=>
    have head:=positive entry (by simp)
    have tail:=ih (by intro e member;exact positive e (by simp [member]))
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul,costs,List.map_cons,List.sum_cons] at tail ⊢
    omega

/--12000 is the source TX_BASE literal; actual intrinsic no-wrap/fee lower
bounds still have to provide this premise for each committed transaction. -/
theorem count_scenario (entries : List Entry) (positive : ∀ entry∈entries,12000≤entry.cost)
    (bounded : costs entries≤200000000) : entries.length≤16666 := by
  have count:=completed_count entries 12000 positive
  omega

def counterAddress : ExpHOL 64:=.op .add [.var .global (ofString "bo"),.const 0#64]
def counterLoad : ExpHOL 64:=.load .one counterAddress
def counterValue : ExpHOL 64:=.op .add [counterLoad,localVar "tx_regular_gas"]
def store : ProgHOL 64:=.store counterAddress counterValue

def findStore : ProgHOL 64→List (ProgHOL 64)
  | p@(.store (.op .add [.var .global name,.const offset]) _)=>
      if name=ofString "bo" ∧ offset=0#64 then [p] else []
  | .seq a b | .ite _ a b=>findStore a++findStore b
  | .dec _ _ _ rest | .decCall _ _ _ _ rest | .while _ rest=>findStore rest
  | _=>[]
def selectedStores : List (ProgHOL 64):=match Guest.guestFn_process_transaction with
  | .function fn=>findStore (progToHOL fn.body)
  | _=>[]

set_option maxRecDepth 10000 in
theorem actual_store : selectedStores=[store] := by
  simp only [selectedStores,Guest.guestFn_process_transaction,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,findStore,↓reduceIte,List.nil_append,List.cons_append,List.append_nil,store,counterAddress,counterValue,counterLoad,localVar]
  rfl

theorem store_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bo before cost : BitVec 64)
    (boGlobal : source.globals.lookup (ofString "bo")=some (.val (.word bo)))
    (costLocal : source.locals.lookup (ofString "tx_regular_gas")=some (.val (.word cost)))
    (mapped : source.memaddrs bo) (stored : source.memory bo=.word before)
    (bounded : before.toNat+cost.toNat≤200000000) :
    evaluateHOLFiniteState source store=(none,{source with memory:=WitnessRadix.StoreWord.put source.memory bo (before+cost)}) ∧
      (before+cost).toNat=before.toNat+cost.toNat := by
  have address : eval source counterAddress=some (.val (.word bo)) := by
    simp [eval,counterAddress,evalHOLExact,evalListHOLExact,toExact,boGlobal,valueIsWord,valueWord,wordOpHOL,wordOp]
  have read : eval source counterLoad=some (.val (.word before)) := by
    simp only [eval] at address ⊢
    simp [counterLoad,evalHOLExact,address,isWfShapeExactHOL,memLoadHOLExact,mapped,stored]
  have value : eval source counterValue=some (.val (.word (before+cost))) := by
    simp only [eval] at read ⊢
    simp only [counterValue,evalHOLExact,evalListHOLExact,read]
    simp [evalHOLExact,toExact,localVar,costLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact ⟨WitnessRadix.StoreWord.execute source counterAddress counterValue bo (before+cost) address value mapped,
    BitVec.toNat_add_of_lt (by omega)⟩

end InitECandidate.Solver.GasBudget.BlockAccounting

#print axioms InitECandidate.Solver.GasBudget.BlockAccounting.regular_cost
#print axioms InitECandidate.Solver.GasBudget.BlockAccounting.regular_bounds
#print axioms InitECandidate.Solver.GasBudget.BlockAccounting.reservation
#print axioms InitECandidate.Solver.GasBudget.BlockAccounting.work_le_cost
#print axioms InitECandidate.Solver.GasBudget.BlockAccounting.aggregate_with_partial
#print axioms InitECandidate.Solver.GasBudget.BlockAccounting.completed_count
#print axioms InitECandidate.Solver.GasBudget.BlockAccounting.count_scenario
#print axioms InitECandidate.Solver.GasBudget.BlockAccounting.actual_store
#print axioms InitECandidate.Solver.GasBudget.BlockAccounting.store_execute
