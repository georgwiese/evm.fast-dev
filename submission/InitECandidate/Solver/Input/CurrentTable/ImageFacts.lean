import InitECandidate.Solver.Input.CurrentTable.Image

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact WitnessRadix

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
variable {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}

theorem Image.node_inside (image : Image source table cap root next count valid bits left right keys ValueOf)
    (node : BitVec 64) (member : valid node) : node.toNat ≤ cap.toNat := by
  have range := (image.validRange node).mp member
  have bound := image.nextBound
  omega

theorem Image.key_arena (image : Image source table cap root next count valid bits left right keys ValueOf)
    (node : BitVec 64) (member : valid node) : AllocatedBytes.Arena (slot (New.keysPointer table) node 32) 32 :=
  image.geometry.key_slot node (image.node_inside node member)

theorem Image.key_fits (image : Image source table cap root next count valid bits left right keys ValueOf)
    (node : BitVec 64) (member : valid node) : (slot (New.keysPointer table) node 32).toNat+32 < 2^64 := by
  have bound := (image.key_arena node member).upper
  omega

theorem Image.next_small (image : Image source table cap root next count valid bits left right keys ValueOf) : next+2 < 2^64 := by
  have capacity := image.geometry.capacityBound
  have bound := image.nextBound
  omega

theorem Image.root_of_member (image : Image source table cap root next count valid bits left right keys ValueOf)
    (node : BitVec 64) (member : valid node) : valid root := by
  rcases image.rootMember with zero | live
  · have empty := image.empty.mp zero
    have bound := image.countNodes
    have range := (image.validRange node).mp member
    omega
  · exact live

/-- The actual builder's sufficient capacity and processed-entry counter
fund both possible new node indices at the current iteration. No future
insertion or allocation success is assumed. -/
theorem Image.two_available (image : Image source table cap root next count valid bits left right keys ValueOf)
    (processed total : Nat) (countBound : count ≤ processed) (active : processed < total)
    (capacity : 2*total+2 ≤ cap.toNat) : next+1 ≤ cap.toNat := by
  have bound := image.countNodes
  omega

theorem Image.fresh_next (image : Image source table cap root next count valid bits left right keys ValueOf) :
    ¬valid (BitVec.ofNat 64 next) := by
  intro member
  have range := (image.validRange (BitVec.ofNat 64 next)).mp member
  have small := image.next_small
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at range
  omega

theorem Image.fresh_next_succ (image : Image source table cap root next count valid bits left right keys ValueOf) :
    ¬valid (BitVec.ofNat 64 (next+1)) := by
  intro member
  have range := (image.validRange (BitVec.ofNat 64 (next+1))).mp member
  have small := image.next_small
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at range
  omega

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.Image.root_of_member
#print axioms InitECandidate.Solver.Input.CurrentTable.Image.two_available
#print axioms InitECandidate.Solver.Input.CurrentTable.Image.fresh_next
#print axioms InitECandidate.Solver.Input.CurrentTable.Image.fresh_next_succ
