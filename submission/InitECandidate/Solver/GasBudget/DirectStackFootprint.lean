import InitECandidate.Solver.GasBudget.DirectStackOpcodeCall
import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.GasBudget.DirectStackOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open MutableTable

def HeaderApart (frame base : BitVec 64) (capacity : Nat) : Prop :=
  ∀ slot < capacity, ∀ offset < 280, ∀ index < 4,
    frame + BitVec.ofNat 64 offset ≠ (base + BitVec.ofNat 64 slot * 32#64) + BitVec.ofNat 64 (8 * index)

theorem relative_number (region : MemoryRegion.Region) (valid : MemoryRegion.Valid region) (offset : Nat) (inside : offset ≤ region.length) :
    (MemoryRegion.pointer region + BitVec.ofNat 64 offset).toNat = region.start + offset := by
  change (WitnessRadix.byteAddress (MemoryRegion.pointer region) offset).toNat = _
  rw [MemoryRegion.byte_address]
  exact MemoryRegion.address_number region valid offset inside

theorem stack_word_number (region : MemoryRegion.Region) (valid : MemoryRegion.Valid region) (capacity : Nat)
    (size : region.length = 32 * capacity) (slot index : Nat) (slotInside : slot < capacity) (inside : index < 4) :
    ((MemoryRegion.pointer region + BitVec.ofNat 64 slot * 32#64) + BitVec.ofNat 64 (8 * index)).toNat = region.start + (slot * 32 + 8 * index) := by
  have address : (MemoryRegion.pointer region + BitVec.ofNat 64 slot * 32#64) + BitVec.ofNat 64 (8 * index) =
      MemoryRegion.pointer region + BitVec.ofNat 64 (slot * 32 + 8 * index) := by
    simp only [BitVec.ofNat_add, BitVec.ofNat_mul]
    exact BitVec.add_assoc _ _ _
  rw [address]
  apply relative_number region valid _
  rw [size]
  omega

/-- Ordinary owned frame/stack reservations discharge every header/stack
alias condition. This is geometric evidence, not global reachability. -/
theorem HeaderApart.of_regions (frame stack : MemoryRegion.Region) (frameValid : MemoryRegion.Valid frame) (stackValid : MemoryRegion.Valid stack)
    (frameSize : 280 ≤ frame.length) (capacity : Nat) (stackSize : stack.length = 32 * capacity)
    (separate : frame.start + frame.length ≤ stack.start ∨ stack.start + stack.length ≤ frame.start) :
    HeaderApart (MemoryRegion.pointer frame) (MemoryRegion.pointer stack) capacity := by
  intro slot slotInside offset offsetInside index inside same
  have frameNumber := relative_number frame frameValid offset (by omega)
  have stackNumber := stack_word_number stack stackValid capacity stackSize slot index slotInside inside
  have numeric := congrArg BitVec.toNat same
  rw [frameNumber, stackNumber] at numeric
  rw [stackSize] at separate
  omega

theorem Footprint.header_words (source target : Memory) (frame base sp : BitVec 64) (capacity pops : Nat)
    (footprint : Footprint source target frame base sp pops) (depthBound : sp.toNat ≤ capacity)
    (positive : 0 < pops) (popsFit : pops ≤ sp.toNat) (owned : HeaderApart frame base capacity) :
    ∀ offset < 280, offset ≠ 0 → offset ≠ 16 → offset ≠ 64 → offset ≠ 184 →
      target (frame + BitVec.ofNat 64 offset) = source (frame + BitVec.ofNat 64 offset) := by
  intro offset inside notPC notSP notGas notUsed
  have different (other : Nat) (small : other < 2 ^ 64) (notEqual : offset ≠ other) :
      frame + BitVec.ofNat 64 offset ≠ frame + BitVec.ofNat 64 other := by
    apply offsets_ne
    intro same
    have numeric := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show offset < 2 ^ 64 from by omega), Nat.mod_eq_of_lt small] at numeric
    exact notEqual numeric
  apply footprint (frame + BitVec.ofNat 64 offset) (different 0 (by decide) notPC) (different 16 (by decide) notSP)
    (different 64 (by decide) notGas) (different 184 (by decide) notUsed)
  exact owned (sp.toNat - pops) (by omega) offset inside

/-- All words outside the two real owned reservations survive. This can
protect separate continuations, journal reservations and live table pools. -/
theorem Footprint.outside_regions (source target : Memory) (frame stack : MemoryRegion.Region)
    (frameValid : MemoryRegion.Valid frame) (stackValid : MemoryRegion.Valid stack) (frameSize : 280 ≤ frame.length)
    (sp : BitVec 64) (capacity pops : Nat) (stackSize : stack.length = 32 * capacity)
    (footprint : Footprint source target (MemoryRegion.pointer frame) (MemoryRegion.pointer stack) sp pops)
    (depthBound : sp.toNat ≤ capacity) (positive : 0 < pops) (popsFit : pops ≤ sp.toNat)
    (query : BitVec 64) (outsideFrame : query.toNat < frame.start ∨ frame.start + frame.length ≤ query.toNat)
    (outsideStack : query.toNat < stack.start ∨ stack.start + stack.length ≤ query.toNat) : target query = source query := by
  have awayFrame (offset : Nat) (inside : offset < 280) : query ≠ MemoryRegion.pointer frame + BitVec.ofNat 64 offset := by
    intro same
    have numeric := congrArg BitVec.toNat same
    rw [relative_number frame frameValid offset (by omega)] at numeric
    omega
  apply footprint query (awayFrame 0 (by decide)) (awayFrame 16 (by decide)) (awayFrame 64 (by decide)) (awayFrame 184 (by decide))
  intro index inside same
  have slotInside : sp.toNat - pops < capacity := by omega
  have numeric := congrArg BitVec.toNat same
  rw [stack_word_number stack stackValid capacity stackSize (sp.toNat - pops) index slotInside inside] at numeric
  rw [stackSize] at outsideStack
  omega

end InitECandidate.Solver.GasBudget.DirectStackOpcode

#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.relative_number
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.stack_word_number
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.HeaderApart.of_regions
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.Footprint.header_words
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.Footprint.outside_regions
