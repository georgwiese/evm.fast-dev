import InitECandidate.Solver.Input.CurrentTable.Set.InsertedKeys
import InitECandidate.Solver.Input.CurrentTable.Set.InsertedEdges

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The complete current physical insertion image survives a fresh
two-node insertion. Entry premises are derived separately from the actual
lookup/search and builder counter; no successful future run is assumed. -/
theorem inserted_image {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value node parent : BitVec 64}
    {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf) :
    Image (insertedState source table cap node parent pointer value next count difference query left) table cap (insertedRoot root parent next)
      (next+2) (count+1) (Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)))
      (Splice.bits bits (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) difference)
      (Splice.side left (BitVec.ofNat 64 (next+1)) parent node (Splice.choice (BitVec.ofNat 64 next) node query difference false))
      (Splice.side right (BitVec.ofNat 64 (next+1)) parent node (Splice.choice (BitVec.ofNat 64 next) node query difference true))
      (Splice.keys keys (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) node query) ValueOf := by
  let state := insertedState source table cap node parent pointer value next count difference query left
  let live := Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1))
  let level := Splice.bits bits (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) difference
  let leftNext := Splice.side left (BitVec.ofNat 64 (next+1)) parent node (Splice.choice (BitVec.ofNat 64 next) node query difference false)
  let rightNext := Splice.side right (BitVec.ofNat 64 (next+1)) parent node (Splice.choice (BitVec.ofNat 64 next) node query difference true)
  let keyNext := Splice.keys keys (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) node query
  have domain : state.memaddrs = InitE.ordinaryDomain :=
    (MemoryMetadata.domain (inserted_metadata source table cap node parent pointer value next count difference query left)).trans data.image.domain
  have routing : Routing live level leftNext rightNext keyNext := Splice.routing data.image.routing data.fresh
  have mapped (index : BitVec 64) (member : live index) (offset : Nat) (small : offset < 32) (aligned : offset%8 = 0) :
      state.memaddrs (FindLeaf.cell (New.nodesPointer table cap) index offset) := by
    have inside := data.valid_inside index member
    exact AllocatedBytes.word_mapped state (slot (New.nodesPointer table cap) index 32) 32 offset domain
      (data.image.geometry.node_slot index inside) small
      (slot_aligned _ index cap 32 data.image.geometry.nodes inside data.image.geometry.nodesAligned (by decide)) aligned
  have nodes : FindLeaf.Nodes state (New.nodesPointer table cap) live level leftNext rightNext := by
    exact ⟨inserted_bit_bound data,fun index member => mapped index member 24 (by decide) (by decide),inserted_bit data,
      fun index member active => mapped index member 8 (by decide) (by decide),
      fun index member active => mapped index member 16 (by decide) (by decide),inserted_left data,inserted_right data,
      fun index member active => Or.inr ⟨routing.leftMember index member active,routing.leftGreater index member active⟩,
      fun index member active => Or.inr ⟨routing.rightMember index member active,routing.rightGreater index member active⟩⟩
  have oldRoot : valid root := data.image.root_of_member node data.fresh.stoppedMember
  have rootNonzero : insertedRoot root parent next ≠ 0#64 := by
    unfold insertedRoot
    split
    · exact data.fresh.internalNonzero
    · exact data.image.routing.nonzero root oldRoot
  have rootLive : live (insertedRoot root parent next) := by
    unfold insertedRoot
    split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl oldRoot
  have nextBound : next+2 ≤ cap.toNat+1 := by have := data.available; omega
  have countNodes : next+2 ≤ 2*(count+1)+1 := by have := data.image.countNodes; omega
  refine ⟨data.image.geometry,data.image.aligned,domain,data.image.capLower,?_,?_,?_,inserted_count data,?_,?_,?_,inserted_root data,inserted_next data,?_,?_,
    by omega,nextBound,data.countRoom,countNodes,?_,Or.inr rootLive,Splice.valid_range data.image,nodes,routing,inserted_key data,inserted_values data⟩
  · simpa only [BitVec.add_zero] using
      (inserted_header data 0 (by decide) (by decide) (by decide) (by decide)).trans (by simpa only [BitVec.add_zero] using data.image.keyLength)
  · exact (inserted_header data 8 (by decide) (by decide) (by decide) (by decide)).trans data.image.stride
  · exact (inserted_header data 16 (by decide) (by decide) (by decide) (by decide)).trans data.image.capacity
  · exact (inserted_header data 32 (by decide) (by decide) (by decide) (by decide)).trans data.image.keysCell
  · exact (inserted_header data 40 (by decide) (by decide) (by decide) (by decide)).trans data.image.nodesCell
  · exact (inserted_header data 48 (by decide) (by decide) (by decide) (by decide)).trans data.image.orderCell
  · exact (inserted_header data 72 (by decide) (by decide) (by decide) (by decide)).trans data.image.freeCell
  · exact (inserted_header data 80 (by decide) (by decide) (by decide) (by decide)).trans data.image.nodeCapacity
  · constructor
    · intro zero
      exact (rootNonzero zero).elim
    · intro impossible
      omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_image
