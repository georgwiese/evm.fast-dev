import InitECandidate.Solver.Mpt.NodeConstructorProgram
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem scalar_tail_quiet (kind : Kind) (scalar : kind≠.branch) (code) : Input.QuietClock.Preserves code (tail kind) := by
  cases kind <;> try exact (scalar rfl).elim
  all_goals simp only [tail,body,original,Guest.Software.guestFn_node_new_hashed,Guest.Software.guestFn_node_new_leaf,Guest.Software.guestFn_node_new_ext,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  all_goals repeat first
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.store code _ _
    | exact Input.QuietClock.returned code _

/-- All original scalar-node constructor outcomes, including allocator trap
guards and failed store reads, cost at most two body source ticks. -/
theorem scalar_body_price (kind : Kind) (scalar : kind≠.branch) (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code (body kind) 2 := by
  rw [allocation_shape]
  exact WitnessRadix.PersistentAlloc.scoped_price code installed (ofString "nd") .one _ _ 0
    (Input.ClockCost.of_quiet code _ (scalar_tail_quiet kind scalar code))

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_tail_quiet
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_body_price
