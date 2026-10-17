import InitECandidate.Solver.GasBudget.Refill
import InitECandidate.Solver.GasBudget.Refund

namespace InitECandidate.Solver.GasBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem ignored_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (fn : MlS) (expressions : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (paid : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some values)
    (called : lookupCodeHOLFinite source.code.lookup fn values=some (body,callee,.one)) (enough : 1≤source.clock)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned (.val (.word 0#64))),target))
    (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid}) :
    evaluateHOLFiniteState source (.call (some (none,none)) fn expressions)=(none,{source with memory:=target.memory,clock:=source.clock-paid}) := by
  have actual:=evaluateHOLFiniteState_call_return_caller_locals source none fn expressions values body callee .one
    (.val (.word 0#64)) target args called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  exact actual.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>(none,state)) callerFrame)

/-- Actual ignored refund caller, including both call clocks and preservation
of the natural regular-gas budget. The reservoir may change independently. -/
theorem refund_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word amount)])
    (code : source.code.lookup (ofString "credit_state_gas_refund")=some (Refund.formals,Refund.body,.one))
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (mapped : ∀ offset∈([64,72,192] : List Nat),source.memaddrs (frame+BitVec.ofNat 64 offset))
    (gasCell : source.memory (frame+64#64)=.word gas) (stateCell : source.memory (frame+72#64)=.word state)
    (spillCell : source.memory (frame+192#64)=.word spill)
    (minCode : source.code.lookup (ofString "min")=some (Minimum.formals,Minimum.body,.one))
    (fits : gas.toNat+spill.toNat<2^64) (enough : 2≤source.clock) :
    ∃ memory,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "credit_state_gas_refund") expressions)=
        (none,{source with memory:=memory,clock:=source.clock-2}) ∧
      regularBudget memory frame=regularBudget source.memory frame := by
  obtain ⟨callee,called,amountLocal⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString "credit_state_gas_refund") "amount" Refund.body amount code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,run,memory,frameEq⟩:=Refund.execute entry frame gas state spill amount ev amountLocal mapped gasCell stateCell spillCell minCode
    (by change 1≤source.clock-1; omega)
  have callerFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-2} := by
    change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-1-1} at frameEq
    have sub : source.clock-1-1=source.clock-2 := by omega
    simpa only [sub] using frameEq
  refine ⟨target.memory,ignored_return source target _ expressions _ Refund.body callee 2 args called (by omega) run callerFrame,?_⟩
  rw [memory]
  exact Refund.preserves_regular_budget source frame gas state spill amount gasCell spillCell fits

/-- Actual ignored rollback-refill caller, with one source call clock and the
same natural regular-gas budget before and after its real memory writes. -/
theorem refill_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame message gas spill reservoir : BitVec 64)
    (code : source.code.lookup (ofString "refill_frame_state_gas")=some ([],Refill.body,.one))
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (mapped : ∀ offset∈([64,72,112,192] : List Nat),source.memaddrs (frame+BitVec.ofNat 64 offset))
    (messageCell : source.memory (frame+112#64)=.word message)
    (gasCell : source.memory (frame+64#64)=.word gas) (spillCell : source.memory (frame+192#64)=.word spill)
    (reservoirMapped : source.memaddrs (message+48#64)) (reservoirCell : source.memory (message+48#64)=.word reservoir)
    (reservoirAway : message+48#64≠frame+64#64) (fits : gas.toNat+spill.toNat<2^64) (enough : 1≤source.clock) :
    ∃ memory,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "refill_frame_state_gas") [])=
        (none,{source with memory:=memory,clock:=source.clock-1}) ∧
      regularBudget memory frame=regularBudget source.memory frame := by
  classical
  have raw : lookupCodeHOLExact source.code.lookup (ofString "refill_frame_state_gas") []=some (Refill.body,(fun _=>none),.one) := by
    simp [lookupCodeHOLExact,code]
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup source.code.lookup (ofString "refill_frame_state_gas") [] Refill.body (fun _=>none) .one raw
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,run,memory,frameEq⟩:=Refill.execute entry frame message gas spill reservoir ev mapped messageCell gasCell spillCell reservoirMapped reservoirCell reservoirAway
  refine ⟨target.memory,ignored_return source target _ [] [] Refill.body callee 1 rfl called enough run frameEq,?_⟩
  rw [memory]
  exact Refill.preserves_regular_budget source frame gas spill reservoir gasCell spillCell fits

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.ignored_return
#print axioms InitECandidate.Solver.GasBudget.refund_call
#print axioms InitECandidate.Solver.GasBudget.refill_call
