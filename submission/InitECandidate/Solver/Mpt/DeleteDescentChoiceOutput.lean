import InitECandidate.Solver.Mpt.DeleteDescentOutput
import InitECandidate.Solver.Mpt.DeleteUnwindModelChoice

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Package an actual terminal assigned helper result. The protected
query supplied here is derived through its genuine memory writes; the
whole pending stack and current key position are preserved. -/
theorem DescentOutput.of_choice (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property)
    (output : ChoiceOutput source target model.pending.graph model.pending.heap limit nodeLower pathLower property)
    (query : output.next.PathBuffer target.be pathLower output.finalHeap.toNat key length.toNat)
    (stopped : model.go=0#64) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  have localFrame (name : String) (other : ofString "res"≠ofString name) : target.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    rw [output.locals]
    simp [HolFiniteMapExact.update,FUPDATE,other]
  let next : DescentModel target key length limit nodeLower pathLower property := {
    pending:=model.pending.after_choice source target limit nodeLower pathLower property output
    node:=model.node
    level:=model.level
    go:=model.go
    keyCell:=(localFrame "key" (by decide)).trans model.keyCell
    lengthCell:=(localFrame "klen" (by decide)).trans model.lengthCell
    nodeCell:=(localFrame "node" (by decide)).trans model.nodeCell
    levelCell:=(localFrame "level" (by decide)).trans model.levelCell
    goCell:=(localFrame "go" (by decide)).trans model.goCell
    goTyped:=model.goTyped
    bounded:=model.bounded
    levelBound:=model.levelBound
    depthBound:=model.depthBound
    nodeMember:=output.old_member source target model.pending.graph model.pending.heap limit nodeLower pathLower property model.node model.nodeMember
    query:=query }
  have frameBefore : model.pending.frame.toNat≤nodeLower:=model.pending.scratch.ordered.trans
    (model.pending.scratchBefore.trans (model.pending.floor.trans model.pending.pathFloor))
  exact ⟨{
    next:=next
    grows:=output.grows
    scratchDecreases:=Nat.le_refl _
    frameEq:=rfl
    members:=output.old_member source target model.pending.graph model.pending.heap limit nodeLower pathLower property
    freshMembers:=by
      intro node member
      rcases (output.members node).1 member with old|same
      · exact Or.inl old
      · rw [same]; exact output.fresh
    fields:=output.fields
    memoryLow:=fun address before=>output.memory address (before.trans_le frameBefore)
    memoryBand:=fun address _ before=>output.memory address before
    protectedWords:=by intro address safe _above before; exact output.protectedWords address safe before
    globals:=fun name other _=>output.globals name other
    progress:=Or.inl stopped }⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.DescentOutput.of_choice
