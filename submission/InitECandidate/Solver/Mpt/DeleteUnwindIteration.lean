import InitECandidate.Solver.Mpt.DeleteUnwindChoiceNormal
import InitECandidate.Solver.Mpt.DeleteUnwindModelPop
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A whole genuinely continuing unwind iteration reads the actual saved
parent, performs its real helper choice, pops PREV and exits the fnode scope.
The resulting physical model has exactly one fewer pending frame. -/
theorem unwind_iteration_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (active : model.top≠0#64)
    (normal : evaluateHOLFiniteState source unwindBody=(none,target)) :
    ∃ next : UnwindModel target limit nodeLower pathLower property,next.frames.length+1=model.frames.length ∧
      model.heap.toNat≤next.heap.toNat ∧ (∀ node,model.graph.valid node→next.graph.valid node) ∧
      model.graph.PathFields target.memory ∧
      (∀ query : BitVec 64,query.toNat<nodeLower→target.memory query=source.memory query) ∧
      (∀ key,key≠ofString "heap_ptr"→target.globals.lookup key=source.globals.lookup key) ∧
      (∀ node,next.graph.valid node→model.graph.valid node ∨ model.heap.toNat≤node.toNat) := by
  obtain ⟨saved,tail,framesEq,topEq,view,_previous,_rest,_decreases⟩:=model.stack.pop source model.cursor.toNat model.top model.frames active
  have owned : saved.Owned model.graph:=model.parents saved (by rw [framesEq]; simp)
  have topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer)):=by rw [←topEq]; exact model.topCell
  have read:=view.node_read source saved model.scratch.domain topCell
  rw [unwind_shapes.2.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "fnode" (field "top" 8#64) saved.node afterFrameNode read normal
  let enteredState:=QueryBranch.bind source "fnode" saved.node
  let entered:=model.bind_other source limit nodeLower pathLower property "fnode" saved.node (by decide) (by decide)
  have enteredView : saved.View enteredState:=view.of_memory source enteredState saved (by intros; rfl)
  have enteredNode : enteredState.locals.lookup (ofString "fnode")=some (.val (.word saved.node)):=bind_lookup_same _ _ _
  rw [unwind_shapes.2.2.1] at continued
  obtain ⟨middle,chosen,popped⟩:=Input.sequence_none enteredState inner unwindChoice pop continued
  obtain ⟨output⟩:=unwind_choice_normal enteredState middle limit nodeLower pathLower property entered saved enteredView owned topEq enteredNode chosen
  let afterChoice:=entered.after_choice enteredState middle limit nodeLower pathLower property output
  have currentActive : afterChoice.top≠0#64:=active
  obtain ⟨finished,heapEq,validEq,decreases⟩:=afterChoice.pop_normal middle inner limit nodeLower pathLower property currentActive popped
  have popFrame : Input.LocalEffects.erase inner=Input.LocalEffects.erase middle:=by
    have actual:=popped
    rw [unwind_shapes.2.2.2.2] at actual
    have frame:=Input.LocalEffects.assign middle.code (ofString "top") (field "top" 0#64) middle rfl
    rw [actual] at frame
    exact frame
  have popMemory:=Input.LocalEffects.memory_of_erase middle inner popFrame
  have popGlobals:=congrArg PanSemStateFiniteExact.globals popFrame
  change inner.globals=middle.globals at popGlobals
  let next:=finished.restore_other source inner limit nodeLower pathLower property "fnode" (by decide) (by decide)
  rw [endpoint]
  refine ⟨next,decreases,?_,?_,?_,?_,?_,?_⟩
  · change model.heap.toNat≤finished.heap.toNat
    rw [heapEq]
    exact output.grows
  · intro node member
    change finished.graph.valid node
    rw [validEq]
    exact (output.members node).2 (Or.inl member)
  · change model.graph.PathFields inner.memory
    rw [popMemory]
    exact output.fields
  · intro query before
    change inner.memory query=source.memory query
    rw [popMemory]
    exact output.memory query before
  · intro key other
    change inner.globals.lookup key=source.globals.lookup key
    rw [popGlobals]
    exact output.globals key other
  · intro node member
    change finished.graph.valid node at member
    rw [validEq] at member
    rcases (output.members node).1 member with old|same
    · exact Or.inl old
    · rw [same]; exact output.fresh

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_iteration_normal
