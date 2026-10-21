import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Ordinary ignored/local/global-result calls spend one caller tick plus
the actual callee allowance, including every assignment/shape failure. -/
theorem assigned_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (destination : Option (VarKind×MlS)) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL) (price : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (priced : (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.call (some (destination,none)) function arguments)).2.clock≤price+1 := by
  rw [evaluateHOLFiniteState_call,args]
  simp only
  rw [called]
  simp only
  by_cases zero : source.clock=0
  · rw [if_pos zero]
    change source.clock-source.clock≤_
    omega
  · rw [if_neg zero]
    have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at priced forward ⊢
    obtain ⟨result,target⟩ := output
    have allowance : source.clock-target.clock≤price+1 := by
      change source.clock-1-target.clock≤price at priced
      change target.clock≤source.clock-1 at forward
      omega
    cases result with
    | none => exact allowance
    | some result =>
      cases result with
      | returned value =>
        simp only
        split
        · cases destination with
          | none => exact allowance
          | some destination =>
            obtain ⟨kind,name⟩ := destination
            dsimp only
            split
            · simpa only [setKvarHOLFinite_clock] using allowance
            · exact allowance
        · exact allowance
      | _ => exact allowance

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.assigned_current
