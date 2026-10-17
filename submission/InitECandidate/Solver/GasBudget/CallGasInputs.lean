import InitECandidate.Solver.GasBudget.CallGasCap

namespace InitECandidate.Solver.GasBudget.CallGas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Inputs (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left : BitVec 64) : Prop where
  value : source.locals.lookup (ofString "value")=some (Input.RlpWrite.U256Value.tuple words)
  gas : source.locals.lookup (ofString "gas")=some (.val (.word requested))
  gasLeft : source.locals.lookup (ofString "gas_left")=some (.val (.word left))
  memory : source.locals.lookup (ofString "memory_cost")=some (.val (.word 0#64))
  extra : source.locals.lookup (ofString "extra_gas")=some (.val (.word 0#64))
def inputNames : List String := ["value","gas","gas_left","memory_cost","extra_gas"]
def temporaryNames : List String := ["vz","stipend","need","avail","mx","g"]
def NameAway (name : String) : Prop := ∀ key∈inputNames,ofString name≠ofString key

theorem temporary_away (name : String) (member : name∈temporaryNames) : NameAway name := by
  intro key input
  simp only [temporaryNames,List.mem_cons,List.mem_singleton] at member
  simp only [inputNames,List.mem_cons,List.mem_singleton] at input
  have temps : name="vz" ∨ name="stipend" ∨ name="need" ∨ name="avail" ∨ name="mx" ∨ name="g" := by simpa using member
  have ins : key="value" ∨ key="gas" ∨ key="gas_left" ∨ key="memory_cost" ∨ key="extra_gas" := by simpa using input
  rcases temps with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases ins with rfl|rfl|rfl|rfl|rfl <;> decide

theorem Inputs.of_locals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left : BitVec 64)
    (same : target.locals=source.locals) (inputs : Inputs source words requested left) : Inputs target words requested left := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals rw [same]
  · exact inputs.value
  · exact inputs.gas
  · exact inputs.gasLeft
  · exact inputs.memory
  · exact inputs.extra

theorem Inputs.bind (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left : BitVec 64)
    (name : String) (word : BitVec 64) (inputs : Inputs source words requested left) (away : NameAway name) :
    Inputs (WitnessRadix.QueryBranch.bind source name word) words requested left := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (bind_lookup_other _ name "value" _ (away _ (by simp [inputNames]))).trans inputs.value
  · exact (bind_lookup_other _ name "gas" _ (away _ (by simp [inputNames]))).trans inputs.gas
  · exact (bind_lookup_other _ name "gas_left" _ (away _ (by simp [inputNames]))).trans inputs.gasLeft
  · exact (bind_lookup_other _ name "memory_cost" _ (away _ (by simp [inputNames]))).trans inputs.memory
  · exact (bind_lookup_other _ name "extra_gas" _ (away _ (by simp [inputNames]))).trans inputs.extra

theorem after_need_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left reward : BitVec 64)
    (inputs : Inputs source words requested left)
    (need : source.locals.lookup (ofString "need")=some (.val (.word 0#64)))
    (rewardLocal : source.locals.lookup (ofString "stipend")=some (.val (.word reward))) :
    ∃ target,evaluateHOLFiniteState source afterNeed=(some (.returned (pair (capped requested left) (capped requested left+reward))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  classical
  have guardRun : evaluateHOLFiniteState source (.ite (.cmp .lower (localVar "gas_left") (localVar "need")) shortage .skip)=(none,source) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,inputs.gasLeft,need,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have availableRead : eval source availableExpression=some (.val (.word left)) := by
    simp [eval,availableExpression,evalHOLExact,evalListHOLExact,toExact,localVar,inputs.gasLeft,inputs.memory,inputs.extra,valueIsWord,valueWord,wordOpHOL,wordOp]
  let sa:=WitnessRadix.QueryBranch.bind source "avail" left
  have enteredInputs:=Inputs.bind source words requested left "avail" left inputs (temporary_away _ (by simp [temporaryNames]))
  have rewardA : sa.locals.lookup (ofString "stipend")=some (.val (.word reward)):=
    (bind_lookup_other _ "avail" "stipend" _ (by decide)).trans rewardLocal
  obtain ⟨target,run,frame⟩:=cap_execute sa requested left reward (bind_lookup_same _ _ _) enteredInputs.gas enteredInputs.extra rewardA
  refine ⟨restore source "avail" target,?_,frame⟩
  rw [afterNeed,WitnessRadix.StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)]
  exact Input.ScalarScope.declare_execute source _ "avail" availableExpression left afterAvail _ availableRead run

theorem after_stipend_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left reward : BitVec 64)
    (inputs : Inputs source words requested left)
    (rewardLocal : source.locals.lookup (ofString "stipend")=some (.val (.word reward)))
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one)) (enough : 1≤source.clock) :
    ∃ target,evaluateHOLFiniteState source afterStipend=(some (.returned (pair (capped requested left) (capped requested left+reward))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "extra_gas",localVar "memory_cost"]=
      some [.val (.word 0#64),.val (.word 0#64)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,inputs.extra,inputs.memory]
  have called:=AddExact.call_execute source 0#64 0#64 "need" [localVar "extra_gas",localVar "memory_cost"] afterNeed args addCode (by decide) enough
  simp only [BitVec.zero_add] at called
  let sn:=WitnessRadix.QueryBranch.bind {source with clock:=source.clock-1} "need" 0#64
  have beforeInputs:=Inputs.of_locals source {source with clock:=source.clock-1} words requested left rfl inputs
  have needInputs:=Inputs.bind _ words requested left "need" 0#64 beforeInputs (temporary_away _ (by simp [temporaryNames]))
  have rewardN : sn.locals.lookup (ofString "stipend")=some (.val (.word reward)):=
    (bind_lookup_other _ "need" "stipend" _ (by decide)).trans rewardLocal
  obtain ⟨target,run,frame⟩:=after_need_execute sn words requested left reward needInputs (bind_lookup_same _ _ _) rewardN
  refine ⟨restore source "need" target,?_,frame⟩
  rw [afterStipend,called,run]

end InitECandidate.Solver.GasBudget.CallGas

#print axioms InitECandidate.Solver.GasBudget.CallGas.temporary_away
#print axioms InitECandidate.Solver.GasBudget.CallGas.Inputs.of_locals
#print axioms InitECandidate.Solver.GasBudget.CallGas.Inputs.bind
#print axioms InitECandidate.Solver.GasBudget.CallGas.after_need_execute
#print axioms InitECandidate.Solver.GasBudget.CallGas.after_stipend_execute
