import InitECandidate.Solver.GasBudget.FrameChargeEvent
import InitECandidate.Solver.GasBudget.CallEntryTable

namespace InitECandidate.Solver.GasBudget
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout MemoryWriter

theorem FrameChargeEvent.header {source ready : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame : BitVec 64} {paid amount : Nat} (event : FrameChargeEvent source ready frame paid amount)
    (aligned : frame.toNat % 8 = 0) (fits : frame.toNat + 280 < 2^64)
    (offset : Nat) (small : offset < 240) (notSP : BitVec.ofNat 64 offset ≠ 16#64)
    (notGas : BitVec.ofNat 64 offset ≠ 64#64) (notUsed : BitVec.ofNat 64 offset ≠ 184#64) :
    ready.memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset) :=
  event.outside _ (offsets_ne frame _ _ notSP) (offsets_ne frame _ _ notGas) (offsets_ne frame _ _ notUsed)
    (AddressMasked.header_away frame offset aligned fits small)

theorem FrameChargeEvent.buffer_view {source ready : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64} {paid amount : Nat}
    (event : FrameChargeEvent source ready frame paid amount)
    (view : MemoryExtend.View source frame base length capacity pointer scratch) (aligned : frame.toNat % 8 = 0) :
    MemoryExtend.View ready frame base length capacity pointer scratch := by
  have current := view.with_memory ready.memory
    ((event.header aligned view.frameFits 24 (by decide) (by decide) (by decide) (by decide)).trans view.baseCell)
    ((event.header aligned view.frameFits 32 (by decide) (by decide) (by decide) (by decide)).trans view.lengthCell)
    ((event.header aligned view.frameFits 40 (by decide) (by decide) (by decide) (by decide)).trans view.capacityCell)
  exact current.after_erase (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) event.fields)

theorem FrameChargeEvent.table {source ready : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame : BitVec 64} {paid amount : Nat} (event : FrameChargeEvent source ready frame paid amount)
    (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (cursor floor : Nat)
    (table : TableState source kind plan slots cursor floor)
    (aligned : frame.toNat % 8 = 0) (fits : frame.toNat + 280 < 2^64) (separate : frame.toNat + 280 ≤ floor) :
    TableState ready kind plan slots cursor floor := by
  have globals := congrArg PanSemStateFiniteExact.globals event.fields
  have domain := congrArg PanSemStateFiniteExact.memaddrs event.fields
  have endian := congrArg PanSemStateFiniteExact.be event.fields
  change ready.globals = source.globals at globals
  change ready.memaddrs = source.memaddrs at domain
  change ready.be = source.be at endian
  apply table.of_pool_frame globals domain endian
  intro pool offset inside
  have number := NaturalLayout.number kind plan table.valid pool offset inside
  have lower := table.lower pool
  have beyondFrame : frame.toNat + 280 ≤ (cell plan pool offset).toNat := by omega
  have apart (field : Nat) (small : field < 280) : cell plan pool offset ≠ frame + BitVec.ofNat 64 field := by
    intro equal
    have same := congrArg BitVec.toNat equal
    have fieldSmall : field < 2^64 := by omega
    have natural : (frame + BitVec.ofNat 64 field).toNat = frame.toNat + field := by
      rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fieldSmall]; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt fieldSmall]
    rw [natural] at same
    omega
  apply event.outside _ (apart 16 (by decide)) (apart 64 (by decide)) (apart 184 (by decide))
  intro byte byteInside equal
  have bounds := AddressMasked.byte_bounds frame byte aligned fits byteInside
  have same := congrArg BitVec.toNat equal
  omega

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.FrameChargeEvent.header
#print axioms InitECandidate.Solver.GasBudget.FrameChargeEvent.buffer_view
#print axioms InitECandidate.Solver.GasBudget.FrameChargeEvent.table
