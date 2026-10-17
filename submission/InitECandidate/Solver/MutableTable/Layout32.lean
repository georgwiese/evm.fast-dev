import InitECandidate.Solver.MutableTable.TableEmptyHeader

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix

inductive Pool where
  | header | keys | values | used | order | position
  deriving DecidableEq

def base (plan : AllocatedLayout.Plan) : Pool→Nat
  | .header=>plan.table
  | .keys=>plan.table+72
  | .values=>plan.table+72+32*plan.capacity
  | .used=>plan.table+72+40*plan.capacity
  | .order=>plan.table+72+41*plan.capacity+plan.padding
  | .position=>plan.table+72+49*plan.capacity+plan.padding

def size (plan : AllocatedLayout.Plan) : Pool→Nat
  | .header=>72
  | .keys=>32*plan.capacity
  | .values | .order | .position=>8*plan.capacity
  | .used=>plan.capacity

def cell (plan : AllocatedLayout.Plan) (pool : Pool) (offset : Nat) : BitVec 64:=
  BitVec.ofNat 64 (base plan pool+offset)

theorem bounds (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (pool : Pool) :
    plan.table≤base plan pool ∧ base plan pool+size plan pool≤plan.table+72+57*plan.capacity+plan.padding := by
  cases pool <;> simp only [base,size] <;> omega

theorem number (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (pool : Pool) (offset : Nat) (inside : offset<size plan pool) :
    (cell plan pool offset).toNat=base plan pool+offset := by
  have bounds:=bounds plan ready pool
  have fits:=ready.fits
  rw [cell,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem base_aligned (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (pool : Pool) :
    base plan pool%8=0 := by
  have aligned:=ready.tableAligned
  have padded:=ready.padded
  cases pool <;> simp only [base] <;> omega

theorem disjoint (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (first second : Pool)
    (different : first≠second) :
    base plan first+size plan first≤base plan second ∨ base plan second+size plan second≤base plan first := by
  cases first <;> cases second <;> simp only [ne_eq,not_true_eq_false] at different <;>
    simp only [base,size] <;> omega

/-- All six actual original-table allocations are disjoint, including the
used-byte array and the short-capacity alignment padding. -/
theorem separate (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (first second : Pool)
    (different : first≠second) (offset other : Nat) (inside : offset<size plan first) (otherInside : other<size plan second) :
    cell plan first offset≠cell plan second other := by
  intro same
  have equal:=congrArg BitVec.toNat same
  rw [number plan ready first offset inside,number plan ready second other otherInside] at equal
  have apart:=disjoint plan ready first second different
  omega

theorem cell_injective (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (pool : Pool)
    (offset other : Nat) (inside : offset<size plan pool) (otherInside : other<size plan pool)
    (different : offset≠other) : cell plan pool offset≠cell plan pool other := by
  intro same
  have equal:=congrArg BitVec.toNat same
  rw [number plan ready pool offset inside,number plan ready pool other otherInside] at equal
  omega

theorem offset_cell (plan : AllocatedLayout.Plan) (pool : Pool) (offset : Nat) :
    BitVec.ofNat 64 (base plan pool)+BitVec.ofNat 64 offset=cell plan pool offset := by
  rw [cell,BitVec.ofNat_add]

/-- The exact aligned cell loaded or written by any array byte. -/
theorem byte_cell (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (pool : Pool)
    (offset : Nat) (inside : offset<size plan pool) :
    panByteAlignHOL (width:=64) (cell plan pool offset)=cell plan pool (8*(offset/8)) := by
  have aligned:=base_aligned plan ready pool
  apply BitVec.eq_of_toNat_eq
  rw [ByteStore.aligned_number,number plan ready pool offset inside,
    number plan ready pool (8*(offset/8)) (by omega)]
  omega

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.separate
#print axioms InitECandidate.Solver.MutableTable.Layout32.cell_injective
#print axioms InitECandidate.Solver.MutableTable.Layout32.byte_cell
