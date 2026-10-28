import InitECandidate.Solver.Input.CurrentTable.Set.FreshAllocationTrace
import InitECandidate.Solver.Input.CurrentTable.NewInternal.Before
import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Memory
import InitECandidate.Solver.Input.CurrentTable.EarlierKey

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value : BitVec 64}
variable {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}

/-- Both actual fresh constructors preserve the earlier decoded input and
query buffer. The complete memory footprint is inside this table's arrays. -/
theorem fresh_before (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (query : BitVec 64) (before : query.toNat < table.toNat) :
    (freshModel source table cap pointer value next count difference).memory query = source.memory query := by
  have small := image.next_small
  have firstInside : (BitVec.ofNat 64 next).toNat ≤ cap.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega
  have secondInside : (BitVec.ofNat 64 (next+1)).toNat ≤ cap.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; exact available
  have countSmall : count < 2^64 := by have := image.countBound; have := image.geometry.capacityBound; omega
  have posInside : (BitVec.ofNat 64 count).toNat ≤ cap.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt countSmall]; exact image.countBound
  rw [freshModel,NewInternal.model_before _ table cap _ _ query image.geometry secondInside before]
  exact NewLeaf.memory_before source table cap _ _ pointer value query image.geometry firstInside posInside before

theorem fresh_query (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (query : KeyBits.Key) (beforeTable : pointer.toNat+32 ≤ table.toNat)
    (view : FirstDiff.ByteView source pointer query) :
    FirstDiff.ByteView (freshModel source table cap pointer value next count difference) pointer query := by
  have domain : (freshModel source table cap pointer value next count difference).memaddrs = source.memaddrs := by
    rw [freshModel,NewInternal.model_domain,NewLeaf.model_domain]
  have endian : (freshModel source table cap pointer value next count difference).be = source.be := by
    rw [freshModel,NewInternal.model_endian,NewLeaf.model_endian]
  exact view.before_frame table.toNat domain endian (fresh_before image available)
    (by have := image.geometry.table.upper; omega) beforeTable

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_before
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_query
