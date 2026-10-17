import InitECandidate.Solver.MutableTable.KeyHash
import InitECandidate.Solver.MutableTable.ByteStore
import InitECandidate.Solver.WitnessRadix.AllocationDomain

namespace InitECandidate.Solver.MutableTable.NaturalLayout
open Flapjack PanSemStateFiniteExact WitnessRadix

inductive Pool where | header | keys | values | used | order | position
  deriving DecidableEq

def stride (kind : KeyHash.Kind) : Nat := 8 * ((KeyHash.keySize kind + 7) / 8)
def rounded (length : Nat) : Nat := 8 * ((length + 7) / 8)

structure Plan where
  base : Pool → Nat
  capacity : Nat

def size (kind : KeyHash.Kind) (plan : Plan) : Pool → Nat
  | .header => 72
  | .keys => stride kind * plan.capacity
  | .used => rounded plan.capacity
  | _ => 8 * plan.capacity

def cell (plan : Plan) (pool : Pool) (offset : Nat) : BitVec 64 := BitVec.ofNat 64 (plan.base pool + offset)

/-- Physical ownership permits separated, relocated arrays after growth as
well as contiguous constructor allocations. Used-byte padding belongs to its
pool, so full-word accesses cannot alias a neighboring array. -/
structure Valid (kind : KeyHash.Kind) (plan : Plan) : Prop where
  positive : 0 < plan.capacity
  lower : ∀ pool, 2701131776 ≤ plan.base pool
  upper : ∀ pool, plan.base pool + size kind plan pool ≤ 33806089496
  aligned : ∀ pool, plan.base pool % 8 = 0
  disjoint : ∀ first second, first ≠ second →
    plan.base first + size kind plan first ≤ plan.base second ∨ plan.base second + size kind plan second ≤ plan.base first

theorem stride_bounds (kind : KeyHash.Kind) : 0 < stride kind ∧ KeyHash.keySize kind ≤ stride kind ∧ stride kind % 8 = 0 := by
  cases kind <;> decide

theorem rounded_bounds (length : Nat) : length ≤ rounded length ∧ rounded length < length + 8 ∧ rounded length % 8 = 0 := by
  unfold rounded
  omega

theorem capacity_small (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) : plan.capacity < 2 ^ 64 := by
  have upper := valid.upper .used
  have roundBound := (rounded_bounds plan.capacity).1
  change plan.base .used + rounded plan.capacity ≤ 33806089496 at upper
  omega

theorem base_number (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (pool : Pool) :
    (cell plan pool 0).toNat = plan.base pool := by
  have upper := valid.upper pool
  simp only [cell, Nat.add_zero, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem number (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (pool : Pool)
    (offset : Nat) (inside : offset < size kind plan pool) : (cell plan pool offset).toNat = plan.base pool + offset := by
  have upper := valid.upper pool
  rw [cell, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem offset_cell (plan : Plan) (pool : Pool) (offset : Nat) :
    byteAddress (cell plan pool 0) offset = cell plan pool offset := by
  simp only [byteAddress, cell, Nat.add_zero, BitVec.ofNat_add]

/-- Actual byte-aligned cell for every pool byte, including partial used
arrays. Full padding is included in the owned size. -/
theorem byte_cell (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (pool : Pool)
    (offset : Nat) (inside : offset < size kind plan pool) :
    panByteAlignHOL (width := 64) (cell plan pool offset) = cell plan pool (8 * (offset / 8)) := by
  have aligned := valid.aligned pool
  apply BitVec.eq_of_toNat_eq
  rw [ByteStore.aligned_number, number kind plan valid pool offset inside,
    number kind plan valid pool (8 * (offset / 8)) (by omega)]
  omega

theorem separate (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (first second : Pool)
    (different : first ≠ second) (offset other : Nat) (inside : offset < size kind plan first) (otherInside : other < size kind plan second) :
    cell plan first offset ≠ cell plan second other := by
  intro equal
  have numeric := congrArg BitVec.toNat equal
  rw [number kind plan valid first offset inside, number kind plan valid second other otherInside] at numeric
  have apart := valid.disjoint first second different
  omega

theorem mapped (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (pool : Pool) (offset : Nat)
    (inside : offset < size kind plan pool) (aligned : offset % 8 = 0) : InitE.ordinaryDomain (cell plan pool offset) := by
  have low := valid.lower pool
  have high := valid.upper pool
  have baseAligned := valid.aligned pool
  apply BackingLayout.ordinary_mapped
  · rw [number kind plan valid pool offset inside]; omega
  · rw [number kind plan valid pool offset inside]; omega
  · rw [number kind plan valid pool offset inside, Nat.add_mod, baseAligned, aligned]

theorem byte_mapped (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (pool : Pool) (offset : Nat)
    (inside : offset < size kind plan pool) : InitE.ordinaryDomain (panByteAlignHOL (width := 64) (cell plan pool offset)) := by
  rw [byte_cell kind plan valid pool offset inside]
  exact mapped kind plan valid pool _ (by omega) (by omega)

end InitECandidate.Solver.MutableTable.NaturalLayout

#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.stride_bounds
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.rounded_bounds
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.capacity_small
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.base_number
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.number
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.offset_cell
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.byte_cell
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.separate
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.mapped
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.byte_mapped
