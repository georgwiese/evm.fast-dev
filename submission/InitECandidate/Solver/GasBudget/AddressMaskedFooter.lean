import InitECandidate.Solver.GasBudget.AddressMaskedProgram
import InitECandidate.Solver.GasBudget.MemoryExtendPopView

namespace InitECandidate.Solver.GasBudget.AddressMasked
open Flapjack PanSemStateFiniteExact WitnessRadix MemoryWriter

theorem byte_bounds (frame : BitVec 64) (offset : Nat) (aligned : frame.toNat % 8 = 0)
    (fits : frame.toNat + 280 < 2^64) (inside : offset < 20) :
    frame.toNat + 240 ≤ (panByteAlignHOL (width := 64) ((frame + 240#64) + BitVec.ofNat 64 offset)).toNat ∧
    (panByteAlignHOL (width := 64) ((frame + 240#64) + BitVec.ofNat 64 offset)).toNat < frame.toNat + 264 := by
  have offsetNumber : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have pointerNumber : (frame + 240#64).toNat = frame.toNat + 240 :=
    BitVec.toNat_add_of_lt (by change frame.toNat + 240 < 2^64; omega)
  have number : ((frame + 240#64) + BitVec.ofNat 64 offset).toNat = frame.toNat + 240 + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [pointerNumber, offsetNumber]; omega), pointerNumber, offsetNumber]
  rw [AllocatedBytes.aligned_number, number]
  have frameDivision := Nat.mod_add_div frame.toNat 8
  have byteDivision := Nat.mod_add_div (frame.toNat + 240 + offset) 8
  have remainder := Nat.mod_lt (frame.toNat + 240 + offset) (by decide : 0 < 8)
  omega

theorem header_away (frame : BitVec 64) (offset : Nat) (aligned : frame.toNat % 8 = 0)
    (fits : frame.toNat + 280 < 2^64) (inside : offset < 240) :
    BytesAway (frame + 240#64) (frame + BitVec.ofNat 64 offset) 20 := by
  intro byte byteInside equal
  have bounds := byte_bounds frame byte aligned fits byteInside
  have offsetNumber : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have queryNumber : (frame + BitVec.ofNat 64 offset).toNat = frame.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [offsetNumber]; omega), offsetNumber]
  have number := congrArg BitVec.toNat equal
  rw [queryNumber] at number
  omega

theorem budget_preserved (before after : Memory) (frame : BitVec 64)
    (aligned : frame.toNat % 8 = 0) (fits : frame.toNat + 280 < 2^64)
    (outside : ∀ query, BytesAway (frame + 240#64) query 20 → after query = before query) :
    regularBudget after frame = regularBudget before frame ∧ after (frame + 184#64) = before (frame + 184#64) := by
  have gas := outside _ (header_away frame 64 aligned fits (by decide))
  have used := outside _ (header_away frame 184 aligned fits (by decide))
  have spill := outside _ (header_away frame 192 aligned fits (by decide))
  exact ⟨by simp only [regularBudget, wordAt, gas, used, spill], used⟩

end InitECandidate.Solver.GasBudget.AddressMasked

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack PanSemStateFiniteExact

theorem View.after_address_masked {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch) (memory : Memory) (name : String) (paid : Nat)
    (aligned : frame.toNat % 8 = 0)
    (outside : ∀ query, MemoryWriter.BytesAway (frame + 240#64) query 20 → memory query = source.memory query) :
    View (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} name (frame + 240#64))
      frame base length capacity pointer scratch := by
  have current := view.with_memory memory
    ((outside _ (AddressMasked.header_away frame 24 aligned view.frameFits (by decide))).trans view.baseCell)
    ((outside _ (AddressMasked.header_away frame 32 aligned view.frameFits (by decide))).trans view.lengthCell)
    ((outside _ (AddressMasked.header_away frame 40 aligned view.frameFits (by decide))).trans view.capacityCell)
  exact current.after_erase rfl

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.AddressMasked.byte_bounds
#print axioms InitECandidate.Solver.GasBudget.AddressMasked.header_away
#print axioms InitECandidate.Solver.GasBudget.AddressMasked.budget_preserved
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.after_address_masked
