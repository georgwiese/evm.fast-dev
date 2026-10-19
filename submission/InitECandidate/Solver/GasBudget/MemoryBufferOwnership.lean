import InitECandidate.Solver.GasBudget.MemoryExtendCall
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.WitnessRadix.ByteStoreWord

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

theorem View.byte_owned {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch) (start : BitVec 64) (count offset : Nat)
    (range : start.toNat + count ≤ length.toNat) (inside : offset < count) :
    let backing := panByteAlignHOL (width := 64) (byteAddress (base + start) offset)
    source.memaddrs backing ∧ base.toNat ≤ backing.toNat ∧ backing.toNat + 8 ≤ scratch.toNat := by
  have extent : base.toNat + length.toNat ≤ scratch.toNat := by
    have depth := view.depth
    have cursor := view.cursor
    have order := BitVec.le_def.mp view.ordered
    omega
  have startFits : base.toNat + start.toNat < 2 ^ 64 := by have bound := scratch.isLt; omega
  have startNumber := BitVec.toNat_add_of_lt startFits
  have byteFits : (base + start).toNat + offset < 2 ^ 64 := by rw [startNumber]; have bound := scratch.isLt; omega
  have byteNumber := byteAddress_toNat (base + start) offset byteFits
  rw [startNumber] at byteNumber
  have backingNumber := AllocatedBytes.aligned_number (byteAddress (base + start) offset)
  have baseDivision := Nat.mod_add_div base.toNat 8
  have scratchDivision := Nat.mod_add_div scratch.toNat 8
  have byteDivision := Nat.mod_add_div (byteAddress (base + start) offset).toNat 8
  have baseAligned := view.baseAligned
  have scratchAligned := view.scratchAligned
  have low : base.toNat ≤ (panByteAlignHOL (width := 64) (byteAddress (base + start) offset)).toNat := by omega
  have high : (panByteAlignHOL (width := 64) (byteAddress (base + start) offset)).toNat + 8 ≤ scratch.toNat := by omega
  have aligned : (panByteAlignHOL (width := 64) (byteAddress (base + start) offset)).toNat % 8 = 0 := by rw [backingNumber]; omega
  exact ⟨view.arena _ low high aligned, low, high⟩

theorem View.byte_away {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch) (start : BitVec 64) (count offset : Nat)
    (range : start.toNat + count ≤ length.toNat) (inside : offset < count)
    (query : BitVec 64) (outside : Arenas.Outside base scratch query) :
    query ≠ panByteAlignHOL (width := 64) (byteAddress (base + start) offset) := by
  obtain ⟨mapped, low, high⟩ := view.byte_owned start count offset range inside
  intro equal
  have number := congrArg BitVec.toNat equal
  rcases outside with before | after <;> omega

theorem View.with_memory {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch) (memory : WordWrites.Memory)
    (baseCell : memory (frame + 24#64) = .word base) (lengthCell : memory (frame + 32#64) = .word length)
    (capacityCell : memory (frame + 40#64) = .word capacity) :
    View {source with memory := memory} frame base length capacity pointer scratch :=
  ⟨view.installed, view.ev, view.mapped, baseCell, lengthCell, capacityCell, view.depth, view.slack,
    view.lengthAligned, view.capacityAligned, view.baseAligned, view.pointerGlobal, view.scratchGlobal,
    view.cursor, view.ordered, view.scratchAligned, view.frameAbove, view.frameFits, view.arena⟩

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.byte_owned
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.byte_away
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.with_memory
