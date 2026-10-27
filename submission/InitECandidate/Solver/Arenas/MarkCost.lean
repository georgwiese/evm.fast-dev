import InitECandidate.Solver.Arenas.Marks

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Price a real mark call and only its exact returned-cursor continuation.
At clock zero the caller stops without needing the continuation bound. -/
theorem mark_price_reached (source : PanSemStateFiniteExact 64 Guest.HostMemory) (direction : Direction)
    (name : String) (pointer : BitVec 64) (continuation : ProgHOL 64) (price : Nat)
    (code : source.code.lookup (ofString (markName direction)) = some ([], markBody direction, .one))
    (stored : source.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer)))
    (tailCost : let ready := bind {source with clock := source.clock - 1} name pointer
      ready.clock - (evaluateHOLFiniteState ready continuation).2.clock ≤ price) :
    source.clock - (evaluateHOLFiniteState source
      (.decCall (ofString name) .one (ofString (markName direction)) [] continuation)).2.clock ≤ price + 1 := by
  by_cases zero : source.clock = 0
  · simp only [zero, Nat.zero_sub]
    exact Nat.zero_le _
  · rw [mark_call source direction name pointer continuation code stored (by omega)]
    let ready := bind {source with clock := source.clock - 1} name pointer
    have forward := evaluateHOLFiniteState_clock_le ready continuation
    change source.clock - (evaluateHOLFiniteState ready continuation).2.clock ≤ price + 1
    change source.clock - 1 - (evaluateHOLFiniteState ready continuation).2.clock ≤ price at tailCost
    change (evaluateHOLFiniteState ready continuation).2.clock ≤ source.clock - 1 at forward
    omega

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.mark_price_reached
