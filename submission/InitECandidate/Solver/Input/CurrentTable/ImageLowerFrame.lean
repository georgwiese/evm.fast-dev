import InitECandidate.Solver.Input.CurrentTable.ImageFacts
import InitECandidate.Solver.Input.CurrentTable.CellGeometry

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Every aligned key byte keeps its physical backing word at or above
the key's real address. Writes strictly below that frontier preserve it. -/
theorem FirstDiff.ByteView.after_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer : BitVec 64} {key : KeyBits.Key} (frontier : Nat)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ address : BitVec 64,frontier≤address.toNat → target.memory address=source.memory address)
    (fits : pointer.toNat+32<2^64) (aligned : pointer.toNat%8=0) (after : frontier≤pointer.toNat)
    (view : FirstDiff.ByteView source pointer key) : FirstDiff.ByteView target pointer key := by
  intro byte
  have number := byteAddress_toNat pointer byte.val (by have := byte.isLt; omega)
  change (pointer+BitVec.ofNat 64 byte.val).toNat=pointer.toNat+byte.val at number
  have backing := AllocatedBytes.aligned_number (pointer+BitVec.ofNat 64 byte.val)
  rw [number] at backing
  have afterCell : frontier≤(panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 byte.val)).toNat := by omega
  have kept := memory _ afterCell
  by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 byte.val))
  all_goals simpa [panMemLoadByteHOL,domain,endian,kept,mapped] using view byte

/-- The complete Patricia image survives unrelated writes below its actual
table address. This includes byte-key backing cells and all physical nodes. -/
theorem Image.of_lower_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ address : BitVec 64,table.toNat≤address.toNat → target.memory address=source.memory address) :
    Image target table cap root next count valid bits left right keys ValueOf := by
  have header (offset : Nat) (small : offset<88) : target.memory (table+BitVec.ofNat 64 offset)=source.memory (table+BitVec.ofNat 64 offset) := by
    apply memory
    have number := byteAddress_toNat table offset (by have := image.geometry.table.upper; omega)
    change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
    omega
  have node (index : BitVec 64) (member : valid index) (offset : Nat) (small : offset<32) :
      target.memory (FindLeaf.cell (New.nodesPointer table cap) index offset)=source.memory (FindLeaf.cell (New.nodesPointer table cap) index offset) :=
    memory _ (by have := image.geometry.cell_after_table index (image.node_inside index member) offset small; omega)
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
  · exact (memory table (Nat.le_refl _)).trans image.keyLength
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
  · intro index member marked
    apply FirstDiff.ByteView.after_frame table.toNat domain endian memory (image.key_fits index member)
      (slot_aligned _ index cap 32 image.geometry.keys (image.node_inside index member) image.geometry.keysAligned (by decide))
      _ (image.leafKeys index member marked)
    rw [slot_number _ index cap 32 image.geometry.keys (image.node_inside index member)]
    have := image.geometry.tableBefore
    omega
  · intro index member marked
    obtain ⟨value,stored,validValue⟩ := image.leafValues index member marked
    exact ⟨value,(node index member 8 (by decide)).trans stored,validValue⟩

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteView.after_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Image.of_lower_frame
