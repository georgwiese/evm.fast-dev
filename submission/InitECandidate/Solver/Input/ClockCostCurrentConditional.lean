import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Price either actual branch at the same current state, including failed
condition evaluation. Branch contracts need no future successful execution. -/
theorem conditional_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (test : ExpHOL 64) (yes no : ProgHOL 64) (yesPrice noPrice : Nat)
    (left : source.clock-(evaluateHOLFiniteState source yes).2.clock≤yesPrice)
    (right : source.clock-(evaluateHOLFiniteState source no).2.clock≤noPrice) :
    source.clock-(evaluateHOLFiniteState source (.ite test yes no)).2.clock≤max yesPrice noPrice := by
  rw [evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) test=value
  cases value with
  | none=>simp
  | some value=>
    cases value with
    | rStruct fields=>simp
    | nStruct name fields=>simp
    | val payload=>
      cases payload with
      | word word=>
        change source.clock-(if word=0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes).2.clock≤max yesPrice noPrice
        by_cases zero : word=0
        · rw [if_pos zero]; exact Nat.le_trans right (Nat.le_max_right _ _)
        · rw [if_neg zero]; exact Nat.le_trans left (Nat.le_max_left _ _)

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.conditional_current
