import InitECandidate.Solver.Mpt.DeleteUnwindModelChoice

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual original pop reconstructs the same current registry and
cursors with one fewer real frame, and the true saved previous top. -/
theorem UnwindModel.pop_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (active : model.top≠0#64)
    (normal : evaluateHOLFiniteState source pop=(none,target)) :
    ∃ next : UnwindModel target limit nodeLower pathLower property,next.heap=model.heap ∧ next.graph.valid=model.graph.valid ∧ next.frames.length+1=model.frames.length := by
  obtain ⟨saved,tail,framesEq,_topEq,endpoint,rest,decreases⟩:=DeleteFrame.pop_normal source target model.cursor.toNat model.top model.frames model.stack active model.topCell model.scratch.domain normal
  have tailParents : DeleteFrame.Parents model.graph tail:=by
    intro current member
    exact model.parents current (by rw [framesEq]; exact List.mem_cons_of_mem saved member)
  rw [endpoint] at rest ⊢
  have tailBound : tail.length≤64:=by have before:=model.bounded; omega
  let next : UnwindModel (QueryBranch.bind source "top" saved.previous) limit nodeLower pathLower property := {
    model with
    top:=saved.previous
    frames:=tail
    topCell:=bind_lookup_same _ _ _
    resultCell:=(bind_lookup_other source "top" "res" saved.previous (by decide)).trans model.resultCell
    scratch:=model.scratch.of_fields source _ model.cursor model.frame rfl rfl
    stack:=rest
    parents:=tailParents
    bounded:=tailBound }
  exact ⟨next,rfl,rfl,decreases⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.UnwindModel.pop_normal
