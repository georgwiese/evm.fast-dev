import InitECandidate.Solver.Mpt.NodeBranchProgram
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.Input.ZeroLiteralCallCost
import InitECandidate.Solver.WitnessRadix.ZeroCost

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A uniform fallback for original branch construction, independent of
heap reachability or mapped memory. The tighter physical bound of nine
ticks remains available when an actual current heap arena is known. -/
theorem branch_uniform_price (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code (body .branch) 228 := by
  have zero : Input.ClockCost.Bound code branchZero 226:=by
    intro source same
    have checked:=Input.ZeroAny.literal_call_cost source (QueryBranch.localVar "nd") 176 (by decide)
      (by rw [same]; exact Zero.original_code code installed)
    exact checked
  have footer:=Input.ClockCost.of_quiet code branchFooter (branch_footer_quiet code)
  have suffix : Input.ClockCost.Bound code (tail .branch) 226:=by
    rw [branch_tail_shape]
    exact Input.ClockCost.sequence code branchZero branchFooter 226 0 zero footer
  rw [allocation_shape]
  exact PersistentAlloc.scoped_price code installed (ofString "nd") .one _ _ 226 suffix

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_uniform_price
