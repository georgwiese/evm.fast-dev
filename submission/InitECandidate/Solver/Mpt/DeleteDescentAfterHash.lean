import InitECandidate.Solver.Mpt.DeleteDescentKindNormal
import InitECandidate.Solver.Mpt.DeleteDescentInvalidate

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Follow the actual ignored cache invalidation before its true kind
dispatch. Its exact caller-local/global frame and derived graph join the
subsequent genuine descent result without assuming future helper success. -/
theorem after_hash_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length tag : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (tagEq : wordAt source.memory model.node=tag) (notHash : tag≠0#64)
    (empty : property 0#64 0#64) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source afterHash=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  rw [descent_shapes.2.2.2.2.2.2.1] at normal
  obtain ⟨middle,invalidated,continued⟩:=Input.sequence_none source target _ _ normal
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "node"]=some [.val (.word model.node)]:=by
    simp [evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,model.nodeCell]
  have bounds:=model.pending.regions model.node model.nodeMember active
  have middleEq:=NodeInvalidate.call_normal source middle model.node [localVar "node"] args model.pending.installed model.pending.scratch.domain
    (AllocatedBytes.Arena.weaken model.node _ 32 bounds.2.1 (TrieWalk.nodeBytes_bounds (wordAt source.memory model.node)).1) bounds.2.2.1 invalidated
  obtain ⟨current,heapEq,cursorEq,frameEq,_framesEq,validEq,nodeEq,levelEq,goEq,fields,memory,_price⟩:=
    invalidate_descent_normal source middle key length limit nodeLower pathLower property model active invalidated
  have currentActive : current.node≠0#64:=by rw [nodeEq]; exact active
  have currentTag : wordAt middle.memory current.node=tag:=by rw [nodeEq]; exact (fields.tags model.node model.nodeMember active).trans tagEq
  have currentCell : middle.locals.lookup (ofString "k")=some (.val (.word tag)):=by rw [middleEq]; exact tagCell
  obtain ⟨output⟩:=kind_output_normal middle target key length tag limit nodeLower pathLower property current currentActive currentCell currentTag notHash empty (goEq.trans stopped) continued
  have currentMembers (node : BitVec 64) (member : model.pending.graph.valid node) : current.pending.graph.valid node:=by rw [validEq]; exact member
  have frameBefore : model.pending.frame.toNat≤nodeLower:=model.pending.scratch.ordered.trans
    (model.pending.scratchBefore.trans (model.pending.floor.trans model.pending.pathFloor))
  exact ⟨{
    next:=output.next
    grows:=by rw [←heapEq]; exact output.grows
    scratchDecreases:=by rw [←cursorEq]; exact output.scratchDecreases
    frameEq:=output.frameEq.trans frameEq
    members:=fun node member=>output.members node (currentMembers node member)
    freshMembers:=by
      intro node member
      rcases output.freshMembers node member with old|fresh
      · exact Or.inl (by rwa [validEq] at old)
      · exact Or.inr (by rwa [heapEq] at fresh)
    fields:=fields.trans model.pending.graph current.pending.graph output.fields currentMembers
    memoryLow:=by
      intro address before
      exact (output.memoryLow address (by rw [frameEq]; exact before)).trans (memory address (before.trans_le frameBefore))
    memoryBand:=by
      intro address above before
      exact (output.memoryBand address (by rw [cursorEq]; exact above) before).trans (memory address before)
    globals:=by
      intro name notHeap notScratch
      have same : middle.globals=source.globals:=by rw [middleEq]; rfl
      exact (output.globals name notHeap notScratch).trans (congrArg (fun globals=>globals.lookup name) same)
    progress:=by
      rcases output.progress with stop|advance
      · exact Or.inl stop
      · exact Or.inr (by rwa [levelEq] at advance) }⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.after_hash_output
