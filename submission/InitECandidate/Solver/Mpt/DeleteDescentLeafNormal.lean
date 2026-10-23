import InitECandidate.Solver.Mpt.DeleteDescentLeafGuard
import InitECandidate.Solver.Mpt.DeleteDescentPathReads
import InitECandidate.Solver.Mpt.DeleteDescentOutputPure
import InitECandidate.Solver.MutableTable.MemeqSmallNonePrefix
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem leaf_length_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=1#64) :
    evaluateHOLFiniteState source leafLengthChoice=
      if wordAt source.memory (model.node+40#64)=length-model.level then evaluateHOLFiniteState source leafCompare else (none,source) := by
  have sizeRead:=(descent_path_reads source key length limit nodeLower pathLower property model active (Or.inl tag)).2
  have remainingRead:=(descent_query_reads source key length limit nodeLower pathLower property model).2
  simp only [eval] at sizeRead remainingRead
  rw [leaf_shapes.2.1,evaluateHOLFiniteState_ite,evalHOLExact,sizeRead,remainingRead]
  by_cases matched : wordAt source.memory (model.node+40#64)=length-model.level <;>
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,matched,evaluateHOLFiniteState_skip]

theorem leaf_compare_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=1#64) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) leafCompareArguments=
      some (MutableTable.MemeqByteRuntime.values (wordAt source.memory (model.node+32#64)) (key+model.level) (length-model.level).toNat) := by
  have pointerRead:=(descent_path_reads source key length limit nodeLower pathLower property model active (Or.inl tag)).1
  obtain ⟨suffixRead,remainingRead⟩:=descent_query_reads source key length limit nodeLower pathLower property model
  simp only [eval] at pointerRead suffixRead remainingRead
  simp only [leafCompareArguments,evalListHOLFinite,evalListHOLExact,pointerRead,suffixRead,remainingRead,MutableTable.MemeqByteRuntime.values]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]

/-- A reached true length match compares the actual complete stored leaf
path and remaining query. Real mapped bytes derive the genuine binary
comparison result, paid prefix and original guard continuation. -/
theorem leaf_compare_model (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=1#64) (matched : wordAt source.memory (model.node+40#64)=length-model.level)
    (normal : evaluateHOLFiniteState source leafCompare=(none,target)) :
    ∃ next : DescentModel target key length limit nodeLower pathLower property,
      next.pending.heap=model.pending.heap ∧ next.pending.cursor=model.pending.cursor ∧ next.pending.frame=model.pending.frame ∧
      next.pending.graph.valid=model.pending.graph.valid ∧ next.go=model.go := by
  have left:=model.pending.paths.span model.node model.nodeMember active (Or.inl tag)
  rw [matched] at left
  have right:=descent_query_suffix source key length limit nodeLower pathLower property model
  have number:=descent_remaining_number source key length limit nodeLower pathLower property model
  have small : (length-model.level).toNat≤64:=by have bounded:=model.bounded; omega
  have args:=leaf_compare_arguments source key length limit nodeLower pathLower property model active tag
  rw [leaf_shapes.2.2.1] at normal
  obtain ⟨paid,answer,inner,_positive,_price,_funded,_binary,continued,endpoint⟩:=MutableTable.MemeqSmall.none_prefix source target
    (wordAt source.memory (model.node+32#64)) (key+model.level) (length-model.level).toNat small left.fits right.span.fits left.mapped right.span.mapped
    (MutableTable.MemeqAny.original_code source.code model.pending.installed) "eq" leafCompareArguments leafCompared args normal
  let paidState:={source with clock:=source.clock-paid}
  let paidModel:=model.with_clock source key length limit nodeLower pathLower property (source.clock-paid)
  let ready:=paidModel.bind_auxiliary paidState key length limit nodeLower pathLower property "eq" answer (by decide)
  have answerCell : (QueryBranch.bind paidState "eq" answer).locals.lookup (ofString "eq")=some (.val (.word answer)):=bind_lookup_same _ _ _
  obtain ⟨next,heapEq,cursorEq,frameEq,members,goEq⟩:=leaf_compared_model (QueryBranch.bind paidState "eq" answer) inner key length limit nodeLower pathLower property ready answer answerCell continued
  let finalModel:=next.restore_auxiliary source inner key length limit nodeLower pathLower property "eq" (by decide)
  rw [endpoint]
  exact ⟨finalModel,heapEq,cursorEq,frameEq,members,goEq⟩

theorem leaf_length_model (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=1#64)
    (normal : evaluateHOLFiniteState source leafLengthChoice=(none,target)) :
    ∃ next : DescentModel target key length limit nodeLower pathLower property,
      next.pending.heap=model.pending.heap ∧ next.pending.cursor=model.pending.cursor ∧ next.pending.frame=model.pending.frame ∧
      next.pending.graph.valid=model.pending.graph.valid ∧ next.go=model.go := by
  rw [leaf_length_dispatch source key length limit nodeLower pathLower property model active tag] at normal
  by_cases matched : wordAt source.memory (model.node+40#64)=length-model.level
  · rw [if_pos matched] at normal
    exact leaf_compare_model source target key length limit nodeLower pathLower property model active tag matched normal
  · rw [if_neg matched] at normal
    have endpoint : target=source:=(congrArg Prod.snd normal).symm
    subst target
    exact ⟨model,rfl,rfl,rfl,rfl,rfl⟩

/-- Whole unchanged254 leaf case, including mismatched length or real
comparison. Its actual registered terminal result retains all physical
query, trie, value, cursor and saved-stack facts. -/
theorem leaf_output_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=1#64) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source leafBlock=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  have pureFrame:=leaf_readonly source.code model.pending.installed source rfl
  rw [normal] at pureFrame
  have nodeRead : eval source (localVar "node")=some (.val (.word model.node)):=by simp [eval,localVar,evalHOLExact,toExact,model.nodeCell]
  have assigned:=assign_result_execute source key length limit nodeLower pathLower property model (localVar "node") model.node nodeRead
  rw [leaf_shapes.1] at normal
  obtain ⟨middle,first,continued⟩:=Input.sequence_none source target _ _ normal
  have middleEq : middle=QueryBranch.bind source "res" model.node:=congrArg Prod.snd (first.symm.trans assigned)
  subst middle
  let selected:=model.bind_result source key length limit nodeLower pathLower property model.node model.nodeMember
  obtain ⟨next,heapEq,cursorEq,frameEq,members,goEq⟩:=leaf_length_model (QueryBranch.bind source "res" model.node) target key length limit nodeLower pathLower property selected active tag continued
  exact DescentOutput.of_erase source target key length limit nodeLower pathLower property model next heapEq cursorEq frameEq members (goEq.trans stopped) pureFrame

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_length_dispatch
#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_compare_arguments
#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_compare_model
#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_length_model
#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_output_normal
