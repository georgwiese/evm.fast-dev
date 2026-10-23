import InitECandidate.Solver.Mpt.DeleteDescentBranchValueNormal
import InitECandidate.Solver.Mpt.DeleteDescentBranchScope

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget

/-- The whole original branch descent case follows its actual level
guard and joins either terminal value deletion or a real nibble push. -/
theorem branch_output_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) (empty : property 0#64 0#64) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source branchBlock=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  rw [branch_dispatch source key length limit nodeLower pathLower property model] at normal
  by_cases done : model.level=length
  · rw [if_pos done] at normal
    exact branch_value_output source target key length limit nodeLower pathLower property model active tag empty stopped normal
  · rw [if_neg done] at normal
    have different : model.level.toNat≠length.toNat:=by intro same; exact done (BitVec.eq_of_toNat_eq same)
    have before : model.level.toNat<length.toNat:=by have bounded:=model.levelBound; omega
    exact branch_scope_output source target key length limit nodeLower pathLower property model active tag before normal

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_output_normal
