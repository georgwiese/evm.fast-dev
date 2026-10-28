import InitECandidate.Solver.Input.CurrentTable.Set.InsertedImage
import InitECandidate.Solver.Input.CurrentTable.Set.FreshInput

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The actual constructor return frame, original image and real parent
link supply the physical entry of the unchanged rewiring block. -/
theorem fresh_ready {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value node parent : BitVec 64}
    {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (frame : LocalEffects.erase target = LocalEffects.erase (freshModel source table cap pointer value next count difference)) :
    target.memaddrs = InitE.ordinaryDomain ∧ target.memory (table+40#64) = .word (New.nodesPointer table cap) ∧
      (parent ≠ 0#64 → target.memory (FindLeaf.cell (New.nodesPointer table cap) parent 8) = .word (left parent)) ∧
      FirstDiff.ByteView target pointer query := by
  have memory := LocalEffects.memory_of_erase _ _ frame
  have domain := LocalEffects.domain_of_erase _ _ frame
  have metadata := fresh_metadata source table cap pointer value next count difference
  refine ⟨domain.trans ((MemoryMetadata.domain metadata).trans data.image.domain),?_,?_,?_⟩
  · rw [memory]
    exact (fresh_header data.image data.available 40 (by decide) (by decide) (by decide)).trans data.image.nodesCell
  · intro nonzero
    obtain ⟨member,active,selected⟩ := data.parent_edges nonzero
    rw [memory,fresh_old_node data.image data.available parent member 8 (by decide)]
    exact data.image.nodes.leftCell parent member active
  · exact (fresh_query data.image data.available query data.beforeTable data.view).of_frame frame

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_ready
