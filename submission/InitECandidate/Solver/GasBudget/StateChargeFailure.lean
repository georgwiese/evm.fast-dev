import InitECandidate.Solver.GasBudget.StateChargeBudget

namespace InitECandidate.Solver.GasBudget.StateCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual unaffordable state charge raises before any gas-pool store.
Its add_sat call is included; no successful charge or fresh budget is assumed. -/
theorem failed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (pools : Pools source frame gas state spill)
    (amountLocal : source.locals.lookup (ofString "amount")=some (.val (.word amount)))
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one))
    (fits : state.toNat+gas.toNat<2^64) (unaffordable : state.toNat+gas.toNat<amount.toNat)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr")=some .one) (enough : 1≤source.clock) :
    ∃ target,evaluateHOLFiniteState source body=(some (.exception (ofString "EvmErr") (.val (.word 4#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
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
  have reservoirTooSmall : state<amount := by change state.toNat<amount.toNat; omega
  have firstRun : evaluateHOLFiniteState entered (.ite firstTest firstBranch .skip)=(none,entered) := by
    rw [evaluateHOLFiniteState_ite]
    simp [firstTest,evalHOLExact,toExact,localVar,stateE,amountE,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,reservoirTooSmall]
  have args : evalListHOLFinite entered (h:=fun address=>Classical.propDecidable (entered.memaddrs address)) [localVar "sgl",localVar "gl"]=
      some [.val (.word state),.val (.word gas)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,stateE,gasE]
  have addRun:=AddExact.call_execute entered state gas "tot" [localVar "sgl",localVar "gl"] afterTotal args addCode fits enough
  let st:=bind {entered with clock:=entered.clock-1} "tot" (state+gas)
  have totalT : st.locals.lookup (ofString "tot")=some (.val (.word (state+gas))):=bind_lookup_same _ _ _
  have amountT : st.locals.lookup (ofString "amount")=some (.val (.word amount)):=
    (bind_lookup_other _ "tot" "amount" _ (by decide)).trans amountE
  have sumTooSmall : state+gas<amount := by change (state+gas).toNat<amount.toNat; rw [BitVec.toNat_add_of_lt fits]; exact unaffordable
  have secondRun : evaluateHOLFiniteState st (.ite totalTest spillCode .skip)=(none,st) := by
    rw [evaluateHOLFiniteState_ite]
    simp [totalTest,evalHOLExact,toExact,localVar,totalT,amountT,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,sumTooSmall]
  have raised : evaluateHOLFiniteState st (.raise (ofString "EvmErr") (.const 4#64))=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite st) := by
    have shapeT : st.eshapes.lookup (ofString "EvmErr")=some .one:=exceptionShape
    simp [evaluateHOLFiniteState_raise,shapeT,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have failedRun : evaluateHOLFiniteState st failure=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite st) := by
    rw [failure,WitnessRadix.StateSteps.stopped_sequence st (emptyLocalsHOLFinite st) _ _ _ raised (Nat.le_refl _)]
  have totalRun : evaluateHOLFiniteState st afterTotal=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite st) := by
    rw [afterTotal,WitnessRadix.StateSteps.next_sequence st st _ _ secondRun (Nat.le_refl _)]
    exact failedRun
  have actual : evaluateHOLFiniteState entered afterPools=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),restore entered "tot" (emptyLocalsHOLFinite st)) := by
    rw [afterPools,WitnessRadix.StateSteps.next_sequence entered entered _ _ firstRun (Nat.le_refl _),addRun,totalRun]
  let final:=restore source "sgl" (restore ss "gl" (restore entered "tot" (emptyLocalsHOLFinite st)))
  refine ⟨final,?_,rfl⟩
  rw [body_shape,WitnessRadix.BuildEntry.declarations_execute setup afterPools,actual]

end InitECandidate.Solver.GasBudget.StateCharge

#print axioms InitECandidate.Solver.GasBudget.StateCharge.failed
