import InitECandidate.Solver.GasBudget.CallGasInputs

namespace InitECandidate.Solver.GasBudget.CallGas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem stipend_update_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left : BitVec 64)
    (inputs : Inputs source words requested left)
    (vz : source.locals.lookup (ofString "vz")=some (.val (.word (U256Zero.resultWord words))))
    (old : source.locals.lookup (ofString "stipend")=some (.val (.word 0#64))) :
    ∃ target,evaluateHOLFiniteState source stipendUpdate=(none,target) ∧
      target={source with locals:=target.locals} ∧ Inputs target words requested left ∧
      target.locals.lookup (ofString "stipend")=some (.val (.word (stipend words))) := by
  classical
  by_cases zero : U256Zero.resultWord words=0#64
  · let target:=WitnessRadix.QueryBranch.bind source "stipend" 2300#64
    have assigned:=WitnessRadix.StateSteps.assign_execute source "stipend" (.const 2300#64) 0#64 2300#64 old rfl
    refine ⟨target,?_,rfl,Inputs.bind source words requested left "stipend" 2300#64 inputs (temporary_away _ (by simp [temporaryNames])),?_⟩
    · rw [stipendUpdate,evaluateHOLFiniteState_ite]
      simpa [evalHOLExact,toExact,localVar,vz,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero] using assigned
    · simpa only [stipend,if_pos zero] using (bind_lookup_same source "stipend" 2300#64)
  · refine ⟨source,?_,rfl,inputs,?_⟩
    · rw [stipendUpdate,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,vz,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
    · simpa only [stipend,if_neg zero] using old

theorem after_zero_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left : BitVec 64)
    (inputs : Inputs source words requested left)
    (vz : source.locals.lookup (ofString "vz")=some (.val (.word (U256Zero.resultWord words))))
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one)) (enough : 1≤source.clock) :
    ∃ target,evaluateHOLFiniteState source afterZero=(some (.returned (pair (capped requested left) (capped requested left+stipend words))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
  let initial:=WitnessRadix.QueryBranch.bind source "stipend" 0#64
  have initialInputs:=Inputs.bind source words requested left "stipend" 0#64 inputs (temporary_away _ (by simp [temporaryNames]))
  have vzI : initial.locals.lookup (ofString "vz")=some (.val (.word (U256Zero.resultWord words))):=
    (bind_lookup_other _ "stipend" "vz" _ (by decide)).trans vz
  obtain ⟨next,updateRun,nextState,nextInputs,reward⟩:=stipend_update_execute initial words requested left initialInputs vzI (bind_lookup_same _ _ _)
  have nextCode:=congrArg PanSemStateFiniteExact.code nextState
  change next.code=source.code at nextCode
  have nextClock:=congrArg PanSemStateFiniteExact.clock nextState
  change next.clock=source.clock at nextClock
  obtain ⟨target,run,frame⟩:=after_stipend_execute next words requested left (stipend words) nextInputs reward (by rw [nextCode]; exact addCode) (by omega)
  have resumed : evaluateHOLFiniteState initial (.seq stipendUpdate afterStipend)=
      (some (.returned (pair (capped requested left) (capped requested left+stipend words))),target) := by
    rw [WitnessRadix.StateSteps.next_sequence initial next _ _ updateRun (by change next.clock≤source.clock; omega)]
    exact run
  refine ⟨restore source "stipend" target,?_,?_⟩
  · rw [afterZero]
    exact Input.ScalarScope.declare_execute source _ "stipend" (.const 0#64) 0#64 _ _ rfl resumed
  · change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1}
    rw [nextState] at frame
    exact frame

/-- Entire actual calculator in the zero-memory/extra-cost mode used by all
four call opcodes. Both real helper calls and all mutable locals/scopes run. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left : BitVec 64)
    (inputs : Inputs source words requested left)
    (zeroCode : source.code.lookup (ofString "u256_is_zero")=some (U256Zero.formals,U256Zero.body,.one))
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one)) (enough : 2≤source.clock) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (pair (capped requested left) (capped requested left+stipend words))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-2} := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "value"]=some [Input.RlpWrite.U256Value.tuple words] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,inputs.value]
  have called:=U256Zero.call_execute source words "vz" [localVar "value"] afterZero args zeroCode (by omega)
  let entered:=WitnessRadix.QueryBranch.bind {source with clock:=source.clock-1} "vz" (U256Zero.resultWord words)
  have beforeInputs:=Inputs.of_locals source {source with clock:=source.clock-1} words requested left rfl inputs
  have enteredInputs:=Inputs.bind _ words requested left "vz" (U256Zero.resultWord words) beforeInputs (temporary_away _ (by simp [temporaryNames]))
  obtain ⟨target,run,frame⟩:=after_zero_execute entered words requested left enteredInputs (bind_lookup_same _ _ _) addCode (by change 1≤source.clock-1; omega)
  refine ⟨restore source "vz" target,?_,?_⟩
  · rw [body_shape,called,run]
  · change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1-1} at frame
    have sub : source.clock-1-1=source.clock-2 := by omega
    change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-2}
    simpa only [sub] using frame

theorem forwarded_number (words : U256Zero.Quad) (requested left : BitVec 64) (fits : left.toNat+2300<2^64) :
    (capped requested left).toNat≤left.toNat ∧
      (capped requested left+stipend words).toNat=(capped requested left).toNat+(stipend words).toNat := by
  have capBound:=(capped_number requested left).2
  have stipendBound:=stipend_bound words
  exact ⟨capBound,BitVec.toNat_add_of_lt (by omega)⟩

end InitECandidate.Solver.GasBudget.CallGas

#print axioms InitECandidate.Solver.GasBudget.CallGas.stipend_update_execute
#print axioms InitECandidate.Solver.GasBudget.CallGas.after_zero_execute
#print axioms InitECandidate.Solver.GasBudget.CallGas.execute
#print axioms InitECandidate.Solver.GasBudget.CallGas.forwarded_number
