import InitECandidate.Solver.Mpt.DeleteDescentLeafCost
import InitECandidate.Solver.Mpt.DeleteDescentExtensionCost
import InitECandidate.Solver.Mpt.DeleteDescentBranchCost
import InitECandidate.Solver.Mpt.DeleteDescentEntry

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A current physical-path allowance for the real kind choice. Copy
work in the terminal branch remains explicit for later amortization. -/
def descentChoiceAllowance (heap : BitVec 64) (pathLower : Nat) : Nat:=max 68 ((heap.toNat-pathLower)/8+40)

theorem kind_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length tag : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (tagEq : wordAt source.memory model.node=tag) (notHash : tag≠0#64) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source kindChoice).2.clock≤descentChoiceAllowance model.pending.heap pathLower := by
  rw [delete_kind_dispatch source tag tagCell]
  by_cases leaf : tag=1#64
  · rw [if_pos leaf]
    exact (leaf_cost source key length limit nodeLower pathLower property model active (tagEq.trans leaf)).trans
      ((by decide : 15≤68).trans (Nat.le_max_left _ _))
  · rw [if_neg leaf]
    by_cases extension : tag=2#64
    · rw [if_pos extension]
      exact (extension_cost source key length limit nodeLower pathLower property model active (tagEq.trans extension)).trans (Nat.le_max_left _ _)
    · rw [if_neg extension]
      have bound:=model.pending.graph.kindBound model.node model.nodeMember active
      rw [tagEq] at bound
      have ne0 : tag.toNat≠0:=by intro equal; exact notHash (BitVec.eq_of_toNat_eq equal)
      have ne1 : tag.toNat≠1:=by intro equal; exact leaf (BitVec.eq_of_toNat_eq equal)
      have ne2 : tag.toNat≠2:=by intro equal; exact extension (BitVec.eq_of_toNat_eq equal)
      have branch : tag=3#64:=BitVec.eq_of_toNat_eq (by change tag.toNat=3; omega)
      exact (branch_cost source key length limit nodeLower pathLower property model active (tagEq.trans branch) empty).trans (Nat.le_max_right _ _)

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.kind_cost
