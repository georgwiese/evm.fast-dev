import InitECandidate.Solver.Input.CurrentTable.FindLeaf.EmptyTable
import InitECandidate.Solver.Input.CurrentTable.Routing
import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteReads
import InitECandidate.Solver.Input.CurrentTable.NewNode.Context
import InitECandidate.Solver.Input.CurrentTable.SlotGeometry

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current insertion-only32-byte table image. Its constructor base is
proved below; actual insertion still has to preserve these physical keys,
node routes, fresh-index range and caller-specific leaf-value predicate. -/
structure Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap root : BitVec 64)
    (next count : Nat) (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat)
    (left right : BitVec 64 → BitVec 64) (keys : BitVec 64 → KeyBits.Key) (ValueOf : BitVec 64 → Prop) : Prop where
  geometry : New.Geometry table cap
  aligned : table.toNat%8 = 0
  domain : source.memaddrs = InitE.ordinaryDomain
  capLower : 2 ≤ cap.toNat
  keyLength : source.memory table = .word 32#64
  stride : source.memory (table+8#64) = .word 32#64
  capacity : source.memory (table+16#64) = .word cap
  countCell : source.memory (table+24#64) = .word (BitVec.ofNat 64 count)
  keysCell : source.memory (table+32#64) = .word (New.keysPointer table)
  nodesCell : source.memory (table+40#64) = .word (New.nodesPointer table cap)
  orderCell : source.memory (table+48#64) = .word (New.orderPointer table cap)
  rootCell : source.memory (table+56#64) = .word root
  nextCell : source.memory (table+64#64) = .word (BitVec.ofNat 64 next)
  freeCell : source.memory (table+72#64) = .word 0#64
  nodeCapacity : source.memory (table+80#64) = .word cap
  nextLower : 1 ≤ next
  nextBound : next ≤ cap.toNat+1
  countBound : count ≤ cap.toNat
  countNodes : next ≤ 2*count+1
  empty : root = 0#64 ↔ count = 0
  rootMember : root = 0#64 ∨ valid root
  validRange : ∀ node,valid node ↔ 1 ≤ node.toNat ∧ node.toNat < next
  nodes : FindLeaf.Nodes source (New.nodesPointer table cap) valid bits left right
  routing : Routing valid bits left right keys
  leafKeys : ∀ node,valid node → bits node = 256 → FirstDiff.ByteView source (slot (New.keysPointer table) node 32) (keys node)
  leafValues : ∀ node,valid node → bits node = 256 →
    ∃ value,source.memory (FindLeaf.cell (New.nodesPointer table cap) node 8) = .word value ∧ ValueOf value

theorem Image.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (frame : LocalEffects.erase target = LocalEffects.erase source) : Image target table cap root next count valid bits left right keys ValueOf := by
  have memory := LocalEffects.memory_of_erase source target frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame
  change target.memaddrs = source.memaddrs at domain
  refine ⟨image.geometry,image.aligned,domain.trans image.domain,image.capLower,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    image.nextLower,image.nextBound,image.countBound,image.countNodes,image.empty,image.rootMember,image.validRange,
    image.nodes.of_frame frame,image.routing,?_,?_⟩
  · rw [memory]; exact image.keyLength
  · rw [memory]; exact image.stride
  · rw [memory]; exact image.capacity
  · rw [memory]; exact image.countCell
  · rw [memory]; exact image.keysCell
  · rw [memory]; exact image.nodesCell
  · rw [memory]; exact image.orderCell
  · rw [memory]; exact image.rootCell
  · rw [memory]; exact image.nextCell
  · rw [memory]; exact image.freeCell
  · rw [memory]; exact image.nodeCapacity
  · intro node member marked
    exact (image.leafKeys node member marked).of_frame frame
  · intro node member marked
    obtain ⟨value,cell,validValue⟩ := image.leafValues node member marked
    exact ⟨value,by rw [memory]; exact cell,validValue⟩

theorem Image.lookup_context {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf) :
    FindLeaf.Context source table (New.nodesPointer table cap) root valid bits left right :=
  ⟨image.nodes,image.rootMember,image.domain,image.geometry.table,image.aligned,image.keyLength,image.nodesCell,image.rootCell⟩

/-- Actual per-call available capacity is supplied separately; this image
alone does not assume room for a future node allocation. -/
theorem Image.allocator_context {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next ≤ cap.toNat) :
    NewNode.Context source table (BitVec.ofNat 64 next) cap := by
  have small : next < 2^64 := by have bound := image.geometry.capacityBound; omega
  exact ⟨image.domain,image.geometry.table,image.aligned,image.freeCell,image.nextCell,image.nodeCapacity,
    by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]; exact available⟩

/-- Every byte/key/value obligation of the actual new empty table is
vacuous. No uninitialized array cells are treated as initialized nodes. -/
theorem image_from_constructor {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table cap stp pad : BitVec 64} (returned : New.Returned source post table cap stp pad) (ValueOf : BitVec 64 → Prop) :
    Image post table cap 0#64 1 0 (fun _ => False) (fun _ => 256) (fun _ => 0#64) (fun _ => 0#64)
      (fun _ _ => 0#8) ValueOf := by
  have field := returned.fields
  have rootCell := field (table+56#64,0#64) (by simp [New.writes])
  have emptyRouting : Routing (fun _ => False) (fun _ => 256) (fun _ => 0#64) (fun _ => 0#64) (fun _ _ => 0#8) := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> intro node impossible <;> exact False.elim impossible
  refine ⟨returned.geometry,returned.tableAligned,returned.arena.domain,returned.capLower,?_,?_,?_,?_,?_,?_,?_,rootCell,?_,?_,?_,
    by decide,by omega,by omega,by decide,by simp,Or.inl rfl,?_,FindLeaf.empty_nodes post _,emptyRouting,?_,?_⟩
  · simpa only [BitVec.add_zero] using field (table+0#64,32#64) (by simp [New.writes])
  · exact field (table+8#64,32#64) (by simp [New.writes])
  · exact field (table+16#64,cap) (by simp [New.writes])
  · exact field (table+24#64,0#64) (by simp [New.writes])
  · exact field (table+32#64,New.keysPointer table) (by simp [New.writes])
  · exact field (table+40#64,New.nodesPointer table cap) (by simp [New.writes])
  · exact field (table+48#64,New.orderPointer table cap) (by simp [New.writes])
  · exact field (table+64#64,1#64) (by simp [New.writes])
  · exact field (table+72#64,0#64) (by simp [New.writes])
  · exact field (table+80#64,cap) (by simp [New.writes])
  · intro node
    constructor
    · intro impossible; exact False.elim impossible
    · intro impossible; omega
  · intro node impossible; exact False.elim impossible
  · intro node impossible; exact False.elim impossible

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.Image.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Image.lookup_context
#print axioms InitECandidate.Solver.Input.CurrentTable.Image.allocator_context
#print axioms InitECandidate.Solver.Input.CurrentTable.image_from_constructor
