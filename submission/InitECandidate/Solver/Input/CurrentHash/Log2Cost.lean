import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.CeilLog2Body
import InitECandidate.Solver.Input.PureReturn
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.CurrentHash.Log2Cost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both actual fuel cases are bounded: enough incoming clock uses the real
execution; otherwise the entire available clock is already below this bound. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (number : BitVec 64) (depth : Nat)
    (small : depth < 64) (bounded : number.toNat ≤ 2^depth)
    (cell : source.locals.lookup (ofString "n") = some (.val (.word number))) :
    source.clock - (evaluateHOLFiniteState source CeilLog2.body).2.clock ≤ depth := by
  by_cases enough : depth ≤ source.clock
  · obtain ⟨post, exponent, bound, ceiling, previous, run, clock, frame⟩ :=
      CeilLog2.body_execute source number depth small bounded enough cell
    rw [run]
    change source.clock - post.clock ≤ depth
    rw [clock]
    omega
  · omega

/-- All outcomes of the genuine current log2 call, with no future return or
minimum clock assumption. Numeric bounds refer to the actual input argument. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS))
    (arguments : List (ExpHOL 64)) (number : BitVec 64) (depth : Nat)
    (small : depth < 64) (bounded : number.toNat ≤ 2^depth)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some [.val (.word number)]) :
    source.clock - (evaluateHOLFiniteState source
      (.call (LocalEffects.callInfo destination) (ofString "ceil_log2") arguments)).2.clock ≤ depth + 1 := by
  obtain ⟨callee, called, cell⟩ := CallNormal.unary_environment source.code.lookup (ofString "ceil_log2") "n" CeilLog2.body number
    (CeilLog2.original_code source.code installed)
  exact ClockCost.call_current source destination (ofString "ceil_log2") arguments [.val (.word number)]
    CeilLog2.body callee .one depth args called
    (body_cost (callEntryStateHOLFinite source callee) number depth small bounded cell)

end InitECandidate.Solver.Input.CurrentHash.Log2Cost

#print axioms InitECandidate.Solver.Input.CurrentHash.Log2Cost.body_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.Log2Cost.call_cost
