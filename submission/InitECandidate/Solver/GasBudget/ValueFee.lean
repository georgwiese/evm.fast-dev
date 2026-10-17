import InitECandidate.Solver.GasBudget.SaturatingAdd

namespace InitECandidate.Solver.GasBudget.ValueFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def arguments : List (ExpHOL 64) := [.op .add [localVar "access_cost",localVar "transfer_cost"],.rfield 0 (localVar "x")]
def charge : ProgHOL 64 := .call (some (none,none)) (ofString "charge_gas") [localVar "need"]
def program (continuation : ProgHOL 64) : ProgHOL 64 := .decCall (ofString "need") .one (ofString "add_sat") arguments (.seq charge continuation)
def fee (access memoryCost : BitVec 64) : BitVec 64 := SaturatingAdd.resultWord (access+11300#64) memoryCost

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (access memoryCost extent : BitVec 64)
    (accessLocal : source.locals.lookup (ofString "access_cost")=some (.val (.word access)))
    (transferLocal : source.locals.lookup (ofString "transfer_cost")=some (.val (.word 11300#64)))
    (x : source.locals.lookup (ofString "x")=some (CallGas.pair memoryCost extent)) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word (access+11300#64)),.val (.word memoryCost)] := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,accessLocal,transferLocal,x,CallGas.pair,
    valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Actual up-front value fee computation and successful charge. Even when
memory-cost addition saturates, its real used-counter credit funds2300 gas. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame left used access memoryCost extent : BitVec 64)
    (accessLocal : source.locals.lookup (ofString "access_cost")=some (.val (.word access)))
    (transferLocal : source.locals.lookup (ofString "transfer_cost")=some (.val (.word 11300#64)))
    (x : source.locals.lookup (ofString "x")=some (CallGas.pair memoryCost extent))
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (gasMapped : source.memaddrs (frame+64#64)) (usedMapped : source.memaddrs (frame+184#64))
    (gasCell : source.memory (frame+64#64)=.word left) (usedCell : source.memory (frame+184#64)=.word used)
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one))
    (chargeCode : source.code.lookup (ofString "charge_gas")=some (RegularCharge.formals,RegularCharge.body,.one))
    (small : access.toNat≤3000) (affordable : fee access memoryCost≤left)
    (fits : left.toNat+used.toNat<2^64) (enough : 2≤source.clock) :
    ∃ target,target=WitnessRadix.QueryBranch.bind {source with memory:=target.memory,clock:=source.clock-2} "need" (fee access memoryCost) ∧
      regularBudget target.memory frame=regularBudget source.memory frame ∧
      2300≤(wordAt target.memory (frame+184#64)).toNat ∧
      (∀ continuation,evaluateHOLFiniteState source (program continuation)=
        (let output:=evaluateHOLFiniteState target continuation;(output.1,restore source "need" output.2))) := by
  have args:=arguments_read source access memoryCost extent accessLocal transferLocal x
  let entered:=WitnessRadix.QueryBranch.bind {source with clock:=source.clock-1} "need" (fee access memoryCost)
  have need : entered.locals.lookup (ofString "need")=some (.val (.word (fee access memoryCost))):=bind_lookup_same _ _ _
  have chargeArgs : evalListHOLFinite entered (h:=fun address=>Classical.propDecidable (entered.memaddrs address)) [localVar "need"]=
      some [.val (.word (fee access memoryCost))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,need]
  obtain ⟨memory,chargeRun,budget,gasDebit,usedCredit⟩:=RegularCharge.call_execute entered frame left used (fee access memoryCost) [localVar "need"] chargeArgs chargeCode ev
    gasMapped usedMapped gasCell usedCell affordable fits (by change 1≤source.clock-1; omega)
  let target:={entered with memory:=memory,clock:=entered.clock-1}
  change evaluateHOLFiniteState entered charge=(none,target) at chargeRun
  have lower : 11300≤(fee access memoryCost).toNat:=SaturatingAdd.value_fee_lower access memoryCost small
  refine ⟨target,?_,budget,by change 2300≤(wordAt memory (frame+184#64)).toNat; omega,?_⟩
  · have sub : source.clock-1-1=source.clock-2 := by omega
    change {source with locals:=entered.locals,memory:=memory,clock:=source.clock-1-1}=
      {source with locals:=entered.locals,memory:=memory,clock:=source.clock-2}
    rw [sub]
  · intro continuation
    have called:=SaturatingAdd.call_execute source (access+11300#64) memoryCost "need" arguments (.seq charge continuation) args addCode (by omega)
    rw [program,called]
    change (let output:=evaluateHOLFiniteState entered (.seq charge continuation);(output.1,restore source "need" output.2))=_
    rw [WitnessRadix.StateSteps.next_sequence entered target _ _ chargeRun (by change entered.clock-1≤entered.clock; omega)]

theorem failed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame left access memoryCost extent : BitVec 64)
    (accessLocal : source.locals.lookup (ofString "access_cost")=some (.val (.word access)))
    (transferLocal : source.locals.lookup (ofString "transfer_cost")=some (.val (.word 11300#64)))
    (x : source.locals.lookup (ofString "x")=some (CallGas.pair memoryCost extent))
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (gasMapped : source.memaddrs (frame+64#64)) (gasCell : source.memory (frame+64#64)=.word left)
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one))
    (chargeCode : source.code.lookup (ofString "charge_gas")=some (RegularCharge.formals,RegularCharge.body,.one))
    (unaffordable : left<fee access memoryCost) (exceptionShape : source.eshapes.lookup (ofString "EvmErr")=some .one) (enough : 2≤source.clock) :
    ∀ continuation,∃ target,evaluateHOLFiniteState source (program continuation)=
        (some (.exception (ofString "EvmErr") (.val (.word 4#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-2} := by
  intro continuation
  let entered:=WitnessRadix.QueryBranch.bind {source with clock:=source.clock-1} "need" (fee access memoryCost)
  have need : entered.locals.lookup (ofString "need")=some (.val (.word (fee access memoryCost))):=bind_lookup_same _ _ _
  have chargeArgs : evalListHOLFinite entered (h:=fun address=>Classical.propDecidable (entered.memaddrs address)) [localVar "need"]=
      some [.val (.word (fee access memoryCost))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,need]
  have chargeRun:=RegularCharge.failed_call entered frame left (fee access memoryCost) [localVar "need"] chargeArgs chargeCode ev gasMapped gasCell unaffordable exceptionShape
    (by change 1≤source.clock-1; omega)
  change evaluateHOLFiniteState entered charge=
    (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite {entered with clock:=entered.clock-1}) at chargeRun
  have stopped : evaluateHOLFiniteState entered (.seq charge continuation)=
      (some (.exception (ofString "EvmErr") (.val (.word 4#64))),emptyLocalsHOLFinite {entered with clock:=entered.clock-1}) := by
    rw [WitnessRadix.StateSteps.stopped_sequence entered _ _ _ _ chargeRun (by change entered.clock-1≤entered.clock; omega)]
  have args:=arguments_read source access memoryCost extent accessLocal transferLocal x
  have called:=SaturatingAdd.call_execute source (access+11300#64) memoryCost "need" arguments (.seq charge continuation) args addCode (by omega)
  refine ⟨restore source "need" (emptyLocalsHOLFinite {entered with clock:=entered.clock-1}),?_,?_⟩
  · rw [program,called]
    change (let output:=evaluateHOLFiniteState entered (.seq charge continuation);(output.1,restore source "need" output.2))=_
    rw [stopped]
  · have sub : source.clock-1-1=source.clock-2 := by omega
    change emptyLocalsHOLFinite {source with clock:=source.clock-1-1}=emptyLocalsHOLFinite {source with clock:=source.clock-2}
    rw [sub]

end InitECandidate.Solver.GasBudget.ValueFee

#print axioms InitECandidate.Solver.GasBudget.ValueFee.arguments_read
#print axioms InitECandidate.Solver.GasBudget.ValueFee.execute
#print axioms InitECandidate.Solver.GasBudget.ValueFee.failed
