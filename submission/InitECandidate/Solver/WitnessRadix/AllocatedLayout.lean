import InitECandidate.Solver.WitnessRadix.AllocationDomain

namespace InitECandidate.Solver.WitnessRadix.AllocatedLayout
open BackingLayout

/-- Exact natural offsets of htab_new's persistent allocations, including
the used-byte array's alignment padding before order. -/
structure Plan where
  table : Nat
  records : Nat
  count : Nat
  capacity : Nat
  padding : Nat

def layout (plan : Plan) : Layout where
  table := BitVec.ofNat 64 plan.table
  keys := BitVec.ofNat 64 (plan.table + 72)
  vals := BitVec.ofNat 64 (plan.table + 72 + 32 * plan.capacity)
  primary := BitVec.ofNat 64 (plan.table + 72 + 41 * plan.capacity + plan.padding)
  backup := BitVec.ofNat 64 (plan.table + 72 + 49 * plan.capacity + plan.padding)
  records := BitVec.ofNat 64 plan.records
  count := plan.count
  capacity := plan.capacity

def baseNat (plan : Plan) : Pool → Nat
  | .header => plan.table
  | .keys => plan.table + 72
  | .vals => plan.table + 72 + 32 * plan.capacity
  | .primary => plan.table + 72 + 41 * plan.capacity + plan.padding
  | .backup => plan.table + 72 + 49 * plan.capacity + plan.padding
  | .records => plan.records

structure Ready (plan : Plan) : Prop where
  room : 2 * plan.count + 2 ≤ plan.capacity
  tableAligned : plan.table % 8 = 0
  recordsAligned : plan.records % 8 = 0
  padded : (plan.capacity + plan.padding) % 8 = 0
  paddingBound : plan.padding < 8
  recordsLower : 2701131776 ≤ plan.records
  recordsBefore : plan.records + 16 * plan.count ≤ plan.table
  fits : plan.table + 72 + 57 * plan.capacity + plan.padding ≤ 33806089496

theorem base_eq (plan : Plan) (pool : Pool) :
    base (layout plan) pool = BitVec.ofNat 64 (baseNat plan pool) := by cases pool <;> rfl

theorem extents (plan : Plan) (ready : Ready plan) (pool : Pool) :
    2701131776 ≤ baseNat plan pool ∧ baseNat plan pool + size (layout plan) pool ≤ 33806089496 := by
  have beforeRecords := ready.recordsBefore
  have lower := ready.recordsLower
  have fits := ready.fits
  cases pool <;> simp only [baseNat, size, layout] <;> omega

theorem base_number (plan : Plan) (ready : Ready plan) (pool : Pool) :
    (base (layout plan) pool).toNat = baseNat plan pool := by
  rw [base_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have bounds := extents plan ready pool
  omega

theorem pool_aligned (plan : Plan) (ready : Ready plan) (pool : Pool) :
    (base (layout plan) pool).toNat % 8 = 0 := by
  rw [base_number plan ready pool]
  have table := ready.tableAligned
  have records := ready.recordsAligned
  have padded := ready.padded
  cases pool <;> simp only [baseNat] <;> omega

theorem disjoint_extents (plan : Plan) (ready : Ready plan) (left right : Pool) (different : left ≠ right) :
    baseNat plan left + size (layout plan) left ≤ baseNat plan right ∨
      baseNat plan right + size (layout plan) right ≤ baseNat plan left := by
  have room := ready.room
  have beforeRecords := ready.recordsBefore
  cases left <;> cases right <;> simp only [ne_eq, not_true_eq_false] at different <;>
    simp only [baseNat, size, layout] <;> omega

/-- The actual allocation order supplies every no-wrap, aligned, positive
and separate-pool premise required by radix construction and lookup. -/
theorem valid (plan : Plan) (ready : Ready plan) : Valid (layout plan) := by
  refine ⟨ready.room, ?_, pool_aligned plan ready, ?_, ?_⟩
  · intro pool
    rw [base_number plan ready pool]
    have bounds := extents plan ready pool
    omega
  · intro pool
    rw [base_number plan ready pool]
    have bounds := extents plan ready pool
    omega
  · intro left right different offset inside other otherInside same
    have leftBounds := extents plan ready left
    have rightBounds := extents plan ready right
    have leftNumber := base_number plan ready left
    have rightNumber := base_number plan ready right
    have leftAddress := byteAddress_toNat (base (layout plan) left) offset (by rw [leftNumber]; omega)
    have rightAddress := byteAddress_toNat (base (layout plan) right) other (by rw [rightNumber]; omega)
    have number := congrArg BitVec.toNat same
    change (byteAddress _ _).toNat = (byteAddress _ _).toNat at number
    rw [leftAddress, rightAddress, leftNumber, rightNumber] at number
    have disjoint := disjoint_extents plan ready left right different
    omega

theorem mapped {F : Type} (source : Flapjack.PanSemStateFiniteExact 64 F) (plan : Plan)
    (ready : Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain) : Mapped source (layout plan) := by
  apply mapped_of_allocated source (layout plan) (valid plan ready) domain
  · intro pool; rw [base_number plan ready pool]; exact (extents plan ready pool).1
  · intro pool; rw [base_number plan ready pool]; exact (extents plan ready pool).2

end InitECandidate.Solver.WitnessRadix.AllocatedLayout

#print axioms InitECandidate.Solver.WitnessRadix.AllocatedLayout.valid
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedLayout.mapped
