import InitECandidate.Solver.Mpt.DeleteDescentModel
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The genuine nonnull-node choice reads its real initialized header
and enters the original k scope. No future dispatch result is assumed. -/
theorem nonnull_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (normal : evaluateHOLFiniteState source nodeChoice=(none,target)) :
    ∃ inner,evaluateHOLFiniteState (QueryBranch.bind source "k" (wordAt source.memory model.node)) afterKind=(none,inner) ∧
      target=restore source "k" inner := by
  have chosen : evaluateHOLFiniteState source nodeChoice=evaluateHOLFiniteState source nonempty:=by
    rw [descent_shapes.2.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,model.nodeCell,active,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨mapped,stored⟩:=model.pending.graph.header model.node model.nodeMember active
  have read : eval source (field "node" 0#64)=some (.val (.word (wordAt source.memory model.node))):=
    DeleteExtension.field_read source "node" model.node 0#64 _ model.nodeCell (by simpa only [BitVec.add_zero] using mapped) (by simpa only [BitVec.add_zero] using stored)
  have actual:=chosen.symm.trans normal
  rw [descent_shapes.2.2.2.1] at actual
  exact Input.declaration_none_word source target "k" (field "node" 0#64) _ afterKind read actual

theorem delete_hash_guard_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source hashGuard=(none,target)) : target=source ∧ tag≠0#64 := by
  by_cases zero : tag=0#64
  · have selected : evaluateHOLFiniteState source hashGuard=evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]):=by
      rw [descent_shapes.2.2.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact (Fail.call_not_normal source target installed _ (selected.symm.trans normal)).elim
  · have skipped : evaluateHOLFiniteState source hashGuard=(none,source):=by
      rw [descent_shapes.2.2.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    exact ⟨congrArg Prod.snd (normal.symm.trans skipped),zero⟩

/-- A true normal after-header continuation must have skipped the hash
failure before reaching original invalidation and node-kind dispatch. -/
theorem after_kind_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterKind=(none,target)) :
    tag≠0#64 ∧ evaluateHOLFiniteState source afterHash=(none,target) := by
  rw [descent_shapes.2.2.2.2.1] at normal
  obtain ⟨middle,first,continued⟩:=Input.sequence_none source target hashGuard afterHash normal
  obtain ⟨middleEq,nonzero⟩:=delete_hash_guard_normal source middle tag tagCell installed first
  subst middle
  exact ⟨nonzero,continued⟩

theorem delete_kind_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag))) :
    evaluateHOLFiniteState source kindChoice=if tag=1#64 then evaluateHOLFiniteState source leafBlock
      else if tag=2#64 then evaluateHOLFiniteState source extensionBlock else evaluateHOLFiniteState source branchBlock := by
  rw [descent_shapes.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_ite]
  by_cases leaf : tag=1#64
  · simp [evalHOLExact,toExact,localVar,tagCell,leaf,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp only [if_neg leaf]
    simp [evalHOLExact,toExact,localVar,tagCell,leaf,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [descent_shapes.2.2.2.2.2.2.2.2,evaluateHOLFiniteState_ite]
    by_cases extension : tag=2#64 <;>
      simp [evalHOLExact,toExact,localVar,tagCell,extension,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.nonnull_entry
#print axioms InitECandidate.Solver.Mpt.DeleteBody.delete_hash_guard_normal
#print axioms InitECandidate.Solver.Mpt.DeleteBody.after_kind_entry
#print axioms InitECandidate.Solver.Mpt.DeleteBody.delete_kind_dispatch
