import InitECandidate.Solver.GasBudget.AddressMaskedFooter
import InitECandidate.Solver.MutableTable.TableStateFrame

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout MemoryWriter

/-- Actual stack-pointer and20byte address-footer writes preserve all six
persistent table pools when the current frame lies below their lifetime floor.
The floor is a current ownership premise, not a future table model. -/
theorem preserve_table {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (frame : BitVec 64) (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (cursor floor : Nat)
    (table : TableState source kind plan slots cursor floor)
    (aligned : frame.toNat % 8 = 0) (fits : frame.toNat + 280 < 2^64) (separate : frame.toNat + 280 ≤ floor)
    (fields : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := target.clock})
    (outside : ∀ query, query ≠ frame + 16#64 → BytesAway (frame + 240#64) query 20 → target.memory query = source.memory query) :
    TableState target kind plan slots cursor floor := by
  have globals := congrArg PanSemStateFiniteExact.globals fields
  have domain := congrArg PanSemStateFiniteExact.memaddrs fields
  have endian := congrArg PanSemStateFiniteExact.be fields
  change target.globals = source.globals at globals
  change target.memaddrs = source.memaddrs at domain
  change target.be = source.be at endian
  apply table.of_pool_frame globals domain endian
  intro pool offset inside
  have number := NaturalLayout.number kind plan table.valid pool offset inside
  have lower := table.lower pool
  have beyondFrame : frame.toNat + 280 ≤ (cell plan pool offset).toNat := by omega
  apply outside
  · intro equal
    have same := congrArg BitVec.toNat equal
    have spNumber : (frame + 16#64).toNat = frame.toNat + 16 := BitVec.toNat_add_of_lt (by change frame.toNat + 16 < 2^64; omega)
    rw [spNumber] at same
    omega
  · intro byte byteInside equal
    have bounds := AddressMasked.byte_bounds frame byte aligned fits byteInside
    have same := congrArg BitVec.toNat equal
    omega

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.preserve_table
