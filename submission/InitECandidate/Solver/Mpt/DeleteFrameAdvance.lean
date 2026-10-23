import InitECandidate.Solver.Mpt.DeleteFrameProgram
import InitECandidate.Solver.Mpt.CollapseBranchScanStep
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Kind.childExpression : Kind→ExpHOL 64
  | .extension=>DeleteBody.field "node" 48#64
  | .branch=>.load .one (DeleteBody.childAddress "node" (localVar "idx"))
def Kind.levelExpression : Kind→ExpHOL 64
  | .extension=>.op .add [localVar "level",localVar "sl"]
  | .branch=>.op .add [localVar "level",.const 1#64]
def advanced (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record child nextLevel : BitVec 64) :=
  QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind source "top" record) "node" child) "level" nextLevel) "go" 1#64

theorem Kind.advance_shape (kind : Kind) : kind.advance=
    .seq (.assign .local (ofString "top") (localVar kind.name))
      (.seq (.assign .local (ofString "node") kind.childExpression)
        (.seq (.assign .local (ofString "level") kind.levelExpression) (.assign .local (ofString "go") (.const 1#64)))) := by
  cases kind <;> rfl

/-- Follow the actual four assignments at the end of either push. The
two read equations refer to the current reached states, not future runs. -/
theorem advance_normal (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record child nextLevel : BitVec 64)
    (recordCell : source.locals.lookup (ofString kind.name)=some (.val (.word record)))
    (childRead : eval (QueryBranch.bind source "top" record) kind.childExpression=some (.val (.word child)))
    (levelRead : eval (QueryBranch.bind (QueryBranch.bind source "top" record) "node" child) kind.levelExpression=some (.val (.word nextLevel)))
    (normal : evaluateHOLFiniteState source kind.advance=(none,target)) : target=advanced source record child nextLevel := by
  have recordRead : eval source (localVar kind.name)=some (.val (.word record)):=by
    simp [eval,localVar,evalHOLExact,toExact,recordCell]
  rw [kind.advance_shape] at normal
  obtain ⟨one,topRun,rest⟩:=Input.sequence_none source target _ _ normal
  have oneEq:=Input.assign_none source one "top" _ record recordRead topRun
  subst one
  obtain ⟨two,nodeRun,rest⟩:=Input.sequence_none _ target _ _ rest
  have twoEq:=Input.assign_none _ two "node" _ child childRead nodeRun
  subst two
  obtain ⟨three,levelRun,goRun⟩:=Input.sequence_none _ target _ _ rest
  have threeEq:=Input.assign_none _ three "level" _ nextLevel levelRead levelRun
  subst three
  exact Input.assign_none _ target "go" (.const 1#64) 1#64 rfl goRun

/-- A matched positive extension consumes actual key nibbles without
wrapping. This progress remains valid for shared or cyclic child graphs. -/
theorem extension_progress (level length segmentLength : BitVec 64)
    (positive : 0<segmentLength.toNat) (matched : segmentLength.toNat≤length.toNat-level.toNat)
    (within : level.toNat≤length.toNat) (small : length.toNat≤64) :
    (level+segmentLength).toNat=level.toNat+segmentLength.toNat ∧
      level.toNat<(level+segmentLength).toNat ∧ (level+segmentLength).toNat≤length.toNat := by
  have addition : (level+segmentLength).toNat=level.toNat+segmentLength.toNat:=BitVec.toNat_add_of_lt (by omega)
  rw [addition]
  omega

theorem branch_progress (level length : BitVec 64) (before : level.toNat<length.toNat) (small : length.toNat≤64) :
    (level+1#64).toNat=level.toNat+1 ∧ level.toNat<(level+1#64).toNat ∧ (level+1#64).toNat≤length.toNat := by
  have addition : (level+1#64).toNat=level.toNat+1:=BitVec.toNat_add_of_lt (by change level.toNat+1<2^64; omega)
  rw [addition]
  omega

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Kind.advance_shape
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.advance_normal
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.extension_progress
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.branch_progress
