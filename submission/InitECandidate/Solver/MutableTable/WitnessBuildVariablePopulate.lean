import InitECandidate.Solver.MutableTable.WitnessBuildPopulate
import InitECandidate.Solver.MutableTable.WitnessBuildBudget

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def tableVariablePrice (slices : Nat → Graph.Slice) (plan : AllocatedLayout.Plan) : Nat :=
  TableNew.price plan.capacity + 1 + recordBudget slices 0 plan.count

/-- Real original table allocation, clearing, complete record loop, return
and lexical scopes. The resulting table represents all actual observed
digest/record pairs in input order, with last-record-wins lookup semantics. -/
theorem table_populate_variable (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (shape : plan.capacity=4 ∨ plan.capacity%8=0)
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (tableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (scratch stp pad : BitVec 64) (slices : Nat→Graph.Slice) (maximum : Nat)
    (recordsLocal : source.locals.lookup (ofString "slice_arr")=some (.val (.word (BitVec.ofNat 64 plan.records))))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 plan.count))))
    (records : Records source plan slices) (context : Context source plan slices stp pad scratch maximum)
    (enough : tableVariablePrice slices plan≤source.clock) :
    ∃ count input logical target,
      evaluateHOLFiniteState source (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64,localVar "cap"] tableTail)=
        (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))),target) ∧
      Layout32.Built bits target plan scratch count input logical ∧ History plan input ∧ input.length=plan.count ∧ Records target plan slices ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl (prepared source plan) ∧
      target.clock≤source.clock ∧ source.clock-tableVariablePrice slices plan≤target.clock := by
  let initial:=prepared source plan
  have domain:=context.environment.domain
  have setupRun:=prepare_execute source plan ready domain shape capLocal heapGlobal tableCode allocCode context.environment.zeroCode
    (by unfold tableVariablePrice at enough;omega)
  obtain ⟨built,locals,recordsData,initialClock⟩:=prepare_data source plan ready domain shape context.little bits scratch recordsLocal countLocal slices records
  have initialContext:=prepared_context source plan slices stp pad scratch maximum context
  obtain ⟨count,input,logical,filled,loopRun,finalBuilt,history,length,finalLocals,finalRecords,control,upper,lower,other⟩:=
    record_loop_variable initial plan ready bits small power scratch stp pad slices maximum 0 plan.count 0 [] (fun _=>none)
      (by simp) rfl built .empty locals recordsData initialContext (by change _≤initial.clock;rw [initialClock];unfold tableVariablePrice at enough;omega)
  have returned : evaluateHOLFiniteState filled (.return (localVar "t"))=
      (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))),emptyLocalsHOLFinite filled) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,finalLocals.table,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have completed : evaluateHOLFiniteState initial (.seq recordLoop (.return (localVar "t")))=
      (some (.returned (.val (.word (BitVec.ofNat 64 plan.table)))),emptyLocalsHOLFinite filled) := by
    rw [StateSteps.next_sequence initial filled _ _ loopRun upper]
    exact returned
  let target:=finishScope source plan (emptyLocalsHOLFinite filled)
  have nextBuilt:=Layout32.built_fields filled target plan bits scratch count input logical rfl rfl rfl finalBuilt
  have nextRecords:=Records.of_earlier filled target plan ready slices (by intros;rfl) finalRecords
  refine ⟨count,input,logical,target,?_,nextBuilt,history,length,nextRecords,control,?_,?_⟩
  · rw [setupRun,completed]
  · change filled.clock≤source.clock
    change filled.clock≤initial.clock at upper
    rw [initialClock] at upper
    omega
  · change source.clock-tableVariablePrice slices plan≤filled.clock
    change initial.clock-recordBudget slices 0 plan.count≤filled.clock at lower
    rw [initialClock] at lower
    unfold tableVariablePrice
    omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.table_populate_variable
