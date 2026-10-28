import InitECandidate.Solver.Input.CurrentTable.NewLeaf.CodeFrame
import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Header
import InitECandidate.Solver.Input.LocalFrameFields

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack PanSemStateFiniteExact

variable {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value : BitVec 64}
variable {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}

/-- The actual fresh-leaf return supplies the next real allocator metadata.
Availability of the second index comes from the caller's processed count,
separately from successful execution of that future allocation. -/
theorem next_allocator (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat)
    (frame : LocalEffects.erase post = LocalEffects.erase (model source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value)) :
    NewNode.Context post table (BitVec.ofNat 64 (next+1)) cap := by
  have small := image.next_small
  have nextInside : (BitVec.ofNat 64 next).toNat ≤ cap.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega
  have countSmall : count < 2^64 := by have := image.geometry.capacityBound; have := image.countBound; omega
  have posInside : (BitVec.ofNat 64 count).toNat ≤ cap.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt countSmall]; exact image.countBound
  have memory := LocalEffects.memory_of_erase _ _ frame
  have domain := LocalEffects.domain_of_erase _ _ frame
  rw [model_domain] at domain
  have header (field : Nat) (inside : field < 88) (notCount : field ≠ 24) (notNext : field ≠ 64) :
      post.memory (table+BitVec.ofNat 64 field) = source.memory (table+BitVec.ofNat 64 field) := by
    rw [memory]
    exact model_header source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value image.geometry nextInside posInside field inside notCount notNext
  refine ⟨domain.trans image.domain,image.geometry.table,image.aligned,
    (header 72 (by decide) (by decide) (by decide)).trans image.freeCell,?_,
    (header 80 (by decide) (by decide) (by decide)).trans image.nodeCapacity,?_⟩
  · rw [memory]
    exact (model_next source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value image.geometry nextInside posInside).trans
      (by rw [BitVec.ofNat_add])
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    exact available

theorem next_nodes (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat)
    (frame : LocalEffects.erase post = LocalEffects.erase (model source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value)) :
    post.memory (table+40#64) = .word (New.nodesPointer table cap) := by
  have small := image.next_small
  have nextInside : (BitVec.ofNat 64 next).toNat ≤ cap.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega
  have countSmall : count < 2^64 := by have := image.geometry.capacityBound; have := image.countBound; omega
  have posInside : (BitVec.ofNat 64 count).toNat ≤ cap.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt countSmall]; exact image.countBound
  rw [LocalEffects.memory_of_erase _ _ frame]
  exact (model_header source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value image.geometry nextInside posInside 40 (by decide) (by decide) (by decide)).trans image.nodesCell

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.next_allocator
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.next_nodes
