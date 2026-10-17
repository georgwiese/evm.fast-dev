import InitECandidate.Solver.MutableTable.NaturalLayoutOwnership

namespace InitECandidate.Solver.MutableTable.NaturalLayout
open Flapjack WitnessRadix

theorem cell_injective (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (pool : Pool)
    (offset other : Nat) (inside : offset < size kind plan pool) (otherInside : other < size kind plan pool)
    (different : offset ≠ other) : cell plan pool offset ≠ cell plan pool other := by
  intro same
  have numeric := congrArg BitVec.toNat same
  rw [number kind plan valid pool offset inside, number kind plan valid pool other otherInside] at numeric
  omega

/-- Key copying preserves each separate owned pool, at both the exact byte
address and aligned physical cell. Used/order/value metadata is protected. -/
theorem pool_key_away (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (query index : BitVec 64)
    (inside : index.toNat < plan.capacity) (pool : Pool) (different : pool ≠ .keys)
    (offset : Nat) (poolInside : offset < size kind plan pool) :
    CopyGeneral.Away ((parameters kind plan query).keys + index * (parameters kind plan query).stride)
      (cell plan pool offset) (KeyHash.keySize kind) := by
  intro byte byteInside
  have addressInside := slot_inside kind plan index.toNat byte inside byteInside
  constructor
  · rw [slot_byte]
    exact separate kind plan valid pool .keys different offset _ poolInside addressInside
  · rw [slot_byte, byte_cell kind plan valid .keys _ addressInside]
    exact separate kind plan valid pool .keys different offset _ poolInside (by omega)

end InitECandidate.Solver.MutableTable.NaturalLayout

#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.cell_injective
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.pool_key_away
