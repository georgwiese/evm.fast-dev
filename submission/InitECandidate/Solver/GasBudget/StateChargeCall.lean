import InitECandidate.Solver.GasBudget.StateChargeFailure

namespace InitECandidate.Solver.GasBudget.StateCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real affordable caller preserves the natural regular budget through
either reservoir payment or regular spill. Both actual call clocks are priced. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word amount)])
    (code : source.code.lookup (ofString "charge_state_gas")=some (formals,body,.one))
    (pools : Pools source frame gas state spill)
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one))
    (fits : state.toNat+gas.toNat<2^64) (regularFits : gas.toNat+spill.toNat<2^64)
    (affordable : amount.toNat≤state.toNat+gas.toNat) (enough : 2≤source.clock) :
    ∃ memory paid,paid≤2 ∧ evaluateHOLFiniteState source (.call (some (none,none)) (ofString "charge_state_gas") expressions)=
        (none,{source with memory:=memory,clock:=source.clock-paid}) ∧
      regularBudget memory frame=regularBudget source.memory frame := by
  obtain ⟨callee,called,amountLocal⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "charge_state_gas") "amount" body amount code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,paid,bound,run,memory,frameEq⟩:=execute entry frame gas state spill amount ⟨pools.ev,pools.mapped,pools.gas,pools.state,pools.spill⟩ amountLocal addCode fits affordable
    (by change 1≤source.clock-1; omega)
  have callerFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-(paid+1)} := by
    change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-1-paid} at frameEq
    have sub : source.clock-1-paid=source.clock-(paid+1) := by omega
    simpa only [sub] using frameEq
  refine ⟨target.memory,paid+1,by omega,ignored_return source target _ expressions _ body callee (paid+1) args called (by omega) run callerFrame,?_⟩
  rw [memory]
  exact preserves_regular_budget source frame gas state spill amount pools affordable regularFits

/-- A real failed charge propagates EvmErr4 with its exact two call clocks and
unchanged memory/control. It cannot enter a normal opcode continuation. -/
theorem failed_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word amount)])
    (code : source.code.lookup (ofString "charge_state_gas")=some (formals,body,.one))
    (pools : Pools source frame gas state spill)
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one))
    (fits : state.toNat+gas.toNat<2^64) (unaffordable : state.toNat+gas.toNat<amount.toNat)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr")=some .one) (enough : 2≤source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "charge_state_gas") expressions)=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite {source with clock:=source.clock-2}) := by
  obtain ⟨callee,called,amountLocal⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "charge_state_gas") "amount" body amount code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,run,frameEq⟩:=failed entry frame gas state spill amount ⟨pools.ev,pools.mapped,pools.gas,pools.state,pools.spill⟩ amountLocal addCode fits unaffordable exceptionShape
    (by change 1≤source.clock-1; omega)
  have actual:=evaluateHOLFiniteState_call_exception_no_handler source none (ofString "charge_state_gas") expressions [.val (.word amount)] body callee .one
    (ofString "EvmErr") (.val (.word 4#64)) target args called (by omega) run
  have sub : source.clock-1-1=source.clock-2 := by omega
  change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1-1} at frameEq
  rw [frameEq,sub] at actual
  exact actual

end InitECandidate.Solver.GasBudget.StateCharge

#print axioms InitECandidate.Solver.GasBudget.StateCharge.call_execute
#print axioms InitECandidate.Solver.GasBudget.StateCharge.failed_call
