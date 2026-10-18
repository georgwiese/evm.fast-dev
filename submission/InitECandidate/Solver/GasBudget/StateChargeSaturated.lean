import InitECandidate.Solver.GasBudget.StateCharge
import InitECandidate.Solver.GasBudget.SaturatingAdd

namespace InitECandidate.Solver.GasBudget.StateCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both actual original affordable charge_state_gas branches, including
saturating overflow of the combined pools. The caller need not supply a
natural-sum fitting premise; only actual affordability and body clock remain. -/
theorem execute_saturated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (pools : Pools source frame gas state spill)
    (amountLocal : source.locals.lookup (ofString "amount")=some (.val (.word amount)))
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one))
    (affordable : amount.toNat≤state.toNat+gas.toNat) (enough : 1≤source.clock) :
    ∃ target paid,paid≤1 ∧ evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),target) ∧
      target.memory=WitnessRadix.WordWrites.write source.memory (poolWrites frame gas state spill amount) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} := by
  classical
  have stateRead:=frame_read source frame 72#64 state pools.ev (pools.mapped 72 (by simp)) pools.state
  let ss:=bind source "sgl" state
  have gasRead:=frame_read ss frame 64#64 gas pools.ev (pools.mapped 64 (by simp)) pools.gas
  let entered:=bind ss "gl" gas
  have setup : WitnessRadix.BuildEntry.Initializes source bindings entered
      (fun output=>restore source "sgl" (restore ss "gl" output)) := .step _ stateRead (.step _ gasRead (.done _))
  have stateE : entered.locals.lookup (ofString "sgl")=some (.val (.word state)):=
    (bind_lookup_other _ "gl" "sgl" _ (by decide)).trans (bind_lookup_same _ _ _)
  have gasE : entered.locals.lookup (ofString "gl")=some (.val (.word gas)):=bind_lookup_same _ _ _
  have amountE : entered.locals.lookup (ofString "amount")=some (.val (.word amount)):=
    (bind_lookup_other _ "gl" "amount" _ (by decide)).trans ((bind_lookup_other _ "sgl" "amount" _ (by decide)).trans amountLocal)
  have enteredPools : Pools entered frame gas state spill:=⟨pools.ev,pools.mapped,pools.gas,pools.state,pools.spill⟩
  have testRead : eval entered firstTest=some (.val (.word (if amount≤state then 1#64 else 0#64))) := by
    simp [eval,firstTest,evalHOLExact,toExact,localVar,stateE,amountE,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at testRead
  by_cases reservoir : amount≤state
  · let target:=emptyLocalsHOLFinite {entered with memory:=WitnessRadix.StoreWord.put entered.memory (frame+72#64) (state-amount)}
    have firstRun : evaluateHOLFiniteState entered (.ite firstTest firstBranch .skip)=(some (.returned (.val (.word 0#64))),target) := by
      rw [evaluateHOLFiniteState_ite,testRead]
      simpa [reservoir] using first_execute entered frame gas state spill amount enteredPools amountE stateE
    have actual : evaluateHOLFiniteState entered afterPools=(some (.returned (.val (.word 0#64))),target) := by
      rw [afterPools,WitnessRadix.StateSteps.stopped_sequence entered target _ _ _ firstRun (Nat.le_refl _)]
    let final:=restore source "sgl" (restore ss "gl" target)
    refine ⟨final,0,by omega,?_,?_,rfl⟩
    · rw [body_shape,WitnessRadix.BuildEntry.declarations_execute setup afterPools,actual]
    · change WitnessRadix.StoreWord.put source.memory (frame+72#64) (state-amount)=WitnessRadix.WordWrites.write source.memory (poolWrites frame gas state spill amount)
      rw [poolWrites,if_pos reservoir]
      rfl
  · have firstRun : evaluateHOLFiniteState entered (.ite firstTest firstBranch .skip)=(none,entered) := by
      rw [evaluateHOLFiniteState_ite,testRead]
      simp [reservoir]
    have args : evalListHOLFinite entered (h:=fun address=>Classical.propDecidable (entered.memaddrs address)) [localVar "sgl",localVar "gl"]=
        some [.val (.word state),.val (.word gas)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,stateE,gasE]
    have addRun:=SaturatingAdd.call_execute entered state gas "tot" [localVar "sgl",localVar "gl"] afterTotal args addCode enough
    let st:=bind {entered with clock:=entered.clock-1} "tot" (SaturatingAdd.resultWord state gas)
    have totalT : st.locals.lookup (ofString "tot")=some (.val (.word (SaturatingAdd.resultWord state gas))):=bind_lookup_same _ _ _
    have amountT : st.locals.lookup (ofString "amount")=some (.val (.word amount)):=
      (bind_lookup_other _ "tot" "amount" _ (by decide)).trans amountE
    have stateT : st.locals.lookup (ofString "sgl")=some (.val (.word state)):=
      (bind_lookup_other _ "tot" "sgl" _ (by decide)).trans stateE
    have gasT : st.locals.lookup (ofString "gl")=some (.val (.word gas)):=
      (bind_lookup_other _ "tot" "gl" _ (by decide)).trans gasE
    have sumNotLess : ¬SaturatingAdd.resultWord state gas<amount := by
      have covered := SaturatingAdd.covers state gas amount affordable
      change amount.toNat ≤ (SaturatingAdd.resultWord state gas).toNat at covered
      change ¬(SaturatingAdd.resultWord state gas).toNat < amount.toNat
      omega
    have totalRead : eval st totalTest=some (.val (.word 1#64)) := by
      simp [eval,totalTest,evalHOLExact,toExact,localVar,totalT,amountT,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,sumNotLess]
    obtain ⟨target,spillRun,memory,frameEq⟩:=spill_execute st frame gas state spill amount ⟨pools.ev,pools.mapped,pools.gas,pools.state,pools.spill⟩ amountT stateT gasT
    have targetClock:=congrArg PanSemStateFiniteExact.clock frameEq
    change target.clock=st.clock at targetClock
    have branchRun : evaluateHOLFiniteState st (.ite totalTest spillCode .skip)=(some (.returned (.val (.word 0#64))),target) := by
      simp only [eval] at totalRead
      rw [evaluateHOLFiniteState_ite,totalRead]
      simpa using spillRun
    have totalRun : evaluateHOLFiniteState st afterTotal=(some (.returned (.val (.word 0#64))),target) := by
      rw [afterTotal,WitnessRadix.StateSteps.stopped_sequence st target _ _ _ branchRun (by omega)]
    have actual : evaluateHOLFiniteState entered afterPools=
        (some (.returned (.val (.word 0#64))),restore entered "tot" target) := by
      rw [afterPools,WitnessRadix.StateSteps.next_sequence entered entered _ _ firstRun (Nat.le_refl _),addRun,totalRun]
    let final:=restore source "sgl" (restore ss "gl" (restore entered "tot" target))
    refine ⟨final,1,by omega,?_,?_,?_⟩
    · rw [body_shape,WitnessRadix.BuildEntry.declarations_execute setup afterPools,actual]
    · change target.memory=WitnessRadix.WordWrites.write source.memory (poolWrites frame gas state spill amount)
      rw [poolWrites,if_neg reservoir]
      exact memory
    · exact frameEq

end InitECandidate.Solver.GasBudget.StateCharge

#print axioms InitECandidate.Solver.GasBudget.StateCharge.execute_saturated
