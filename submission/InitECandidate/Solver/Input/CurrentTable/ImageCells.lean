import InitECandidate.Solver.Input.CurrentTable.ImageFacts

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Reuse a physical image after preserving exactly the header, live node
cells and leaf-key bytes which that image actually observes. -/
theorem Image.of_cells {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (domain : target.memaddrs=source.memaddrs)
    (header : ∀ offset<88,target.memory (table+BitVec.ofNat 64 offset)=source.memory (table+BitVec.ofNat 64 offset))
    (node : ∀ index,valid index → ∀ offset<32,
      target.memory (FindLeaf.cell (New.nodesPointer table cap) index offset)=source.memory (FindLeaf.cell (New.nodesPointer table cap) index offset))
    (keyViews : ∀ index,valid index → bits index=256 → FirstDiff.ByteView target (slot (New.keysPointer table) index 32) (keys index)) :
    Image target table cap root next count valid bits left right keys ValueOf := by
  have nodes : FindLeaf.Nodes target (New.nodesPointer table cap) valid bits left right := by
    refine ⟨image.nodes.bitBound,?_,?_,?_,?_,?_,?_,image.nodes.leftOrdered,image.nodes.rightOrdered⟩
    · intro index member; rw [domain]; exact image.nodes.bitMapped index member
    · intro index member; rw [node index member 24 (by decide)]; exact image.nodes.bitCell index member
    · intro index member internal; rw [domain]; exact image.nodes.leftMapped index member internal
    · intro index member internal; rw [domain]; exact image.nodes.rightMapped index member internal
    · intro index member internal; rw [node index member 8 (by decide)]; exact image.nodes.leftCell index member internal
    · intro index member internal; rw [node index member 16 (by decide)]; exact image.nodes.rightCell index member internal
  refine ⟨image.geometry,image.aligned,domain.trans image.domain,image.capLower,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    image.nextLower,image.nextBound,image.countBound,image.countNodes,image.empty,image.rootMember,image.validRange,nodes,image.routing,?_,?_⟩
  · have kept : target.memory table=source.memory table := by simpa only [BitVec.add_zero] using header 0 (by decide)
    exact kept.trans image.keyLength
  · exact (header 8 (by decide)).trans image.stride
  · exact (header 16 (by decide)).trans image.capacity
  · exact (header 24 (by decide)).trans image.countCell
  · exact (header 32 (by decide)).trans image.keysCell
  · exact (header 40 (by decide)).trans image.nodesCell
  · exact (header 48 (by decide)).trans image.orderCell
  · exact (header 56 (by decide)).trans image.rootCell
  · exact (header 64 (by decide)).trans image.nextCell
  · exact (header 72 (by decide)).trans image.freeCell
  · exact (header 80 (by decide)).trans image.nodeCapacity
  · exact keyViews
  · intro index member marked
    obtain ⟨value,stored,validValue⟩ := image.leafValues index member marked
    exact ⟨value,(node index member 8 (by decide)).trans stored,validValue⟩

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.Image.of_cells
