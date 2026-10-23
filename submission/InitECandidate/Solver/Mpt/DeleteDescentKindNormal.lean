import InitECandidate.Solver.Mpt.DeleteDescentLeafNormal
import InitECandidate.Solver.Mpt.DeleteDescentExtensionNormal
import InitECandidate.Solver.Mpt.DeleteDescentBranchNormal
import InitECandidate.Solver.Mpt.DeleteDescentEntry

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual post-invalidation kind dispatch joins the three original
cases. The genuine initialized tag bound identifies the branch tag3. -/
theorem kind_output_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length tag : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (tagEq : wordAt source.memory model.node=tag) (notHash : tag≠0#64)
    (empty : property 0#64 0#64) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source kindChoice=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  rw [delete_kind_dispatch source tag tagCell] at normal
  by_cases leaf : tag=1#64
  · rw [if_pos leaf] at normal
    exact leaf_output_normal source target key length limit nodeLower pathLower property model active (tagEq.trans leaf) stopped normal
  · rw [if_neg leaf] at normal
    by_cases extension : tag=2#64
    · rw [if_pos extension] at normal
      exact extension_output_normal source target key length limit nodeLower pathLower property model active (tagEq.trans extension) stopped normal
    · rw [if_neg extension] at normal
      have bound:=model.pending.graph.kindBound model.node model.nodeMember active
      rw [tagEq] at bound
      have ne0 : tag.toNat≠0:=by intro equal; exact notHash (BitVec.eq_of_toNat_eq equal)
      have ne1 : tag.toNat≠1:=by intro equal; exact leaf (BitVec.eq_of_toNat_eq equal)
      have ne2 : tag.toNat≠2:=by intro equal; exact extension (BitVec.eq_of_toNat_eq equal)
      have branch : tag=3#64:=BitVec.eq_of_toNat_eq (by change tag.toNat=3; omega)
      exact branch_output_normal source target key length limit nodeLower pathLower property model active (tagEq.trans branch) empty stopped normal

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.kind_output_normal
