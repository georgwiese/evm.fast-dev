import InitECandidate.Solver.Rlp.HeaderCallNormal

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Price the actual header continuation from its real validated result
and exact canonical caller state. This rule permits callers to establish
their own current input/arena facts at that state. -/
theorem scoped_valid_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (installed : Input.OriginalCode.Installed source.code)
    (tail : ∀ paid answer,Valid length.toNat answer →
      (source.clock-paid)-(evaluateHOLFiniteState (setVarHOLFinite (ofString name) answer {source with clock:=source.clock-paid}) continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item_header") arguments continuation)).2.clock≤11+tailPrice := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := environment source.code.lookup pointer length (original_code source.code installed)
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  simp only [args,called]
  by_cases zero : source.clock=0
  · rw [if_pos zero]
    change source.clock-source.clock≤_
    omega
  · rw [if_neg zero]
    have bodyCost := body_cost (callEntryStateHOLFinite source callee) pointer pointerLocal installed
    have bodyClock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at bodyCost bodyClock ⊢
    obtain ⟨result,target⟩ := output
    have cost : source.clock-target.clock≤11+tailPrice := by
      change source.clock-1-target.clock≤10 at bodyCost
      change target.clock≤source.clock-1 at bodyClock
      omega
    cases result with
    | none => exact cost
    | some result =>
      cases result with
      | returned answer =>
        simp only
        split
        · obtain ⟨paid,minimum,maximum,funded,valid,canonical⟩ := callee_resume source target pointer length callee pointerLocal lengthLocal (by omega) installed answer computed
          have priced := tail paid answer valid
          have resumed := canonical name
          rw [←resumed] at priced
          let ready := Input.CallNormal.continuationEntry source target name answer
          have clockEq : source.clock-paid=target.clock := congrArg PanSemStateFiniteExact.clock resumed.symm
          rw [clockEq] at priced
          have clock := evaluateHOLFiniteState_clock_le ready continuation
          change target.clock-(evaluateHOLFiniteState ready continuation).2.clock≤tailPrice at priced
          change (evaluateHOLFiniteState ready continuation).2.clock≤target.clock at clock
          change source.clock-(evaluateHOLFiniteState ready continuation).2.clock≤_
          change source.clock-1-target.clock≤10 at bodyCost
          change target.clock≤source.clock-1 at bodyClock
          omega
        · exact cost
      | error => exact cost
      | timeOut => exact cost
      | «break» => exact cost
      | «continue» => exact cost
      | exception identifier payload => exact cost
      | finalFfi event => exact cost

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.scoped_valid_cost
