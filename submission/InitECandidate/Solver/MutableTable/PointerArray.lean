import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.MutableTable
open Flapjack PanSemStateFiniteExact WitnessRadix

def pointerCell (start index : Nat) : BitVec 64 := BitVec.ofNat 64 (start + 8 * index)

/-- Actual owned array of pointers to logical query bytes. Its word reads
and query mappings are carried through mutations by the lifetime floor. -/
structure PointerArray (memory : WordWrites.Memory) (width start count floor : Nat) (pointers : Nat → BitVec 64) : Prop where
  valid : MemoryRegion.Valid ⟨start, 8 * count⟩
  earlier : start + 8 * count ≤ floor
  words : ∀ index < count, memory (pointerCell start index) = .word (pointers index)
  fits : ∀ index < count, (pointers index).toNat + width < 2 ^ 64
  mapped : ∀ index < count, ∀ offset < width, InitE.ordinaryDomain (panByteAlignHOL (width := 64) (byteAddress (pointers index) offset))

theorem PointerArray.cell_number {memory : WordWrites.Memory} {width start count floor : Nat} {pointers : Nat → BitVec 64}
    (array : PointerArray memory width start count floor pointers) (index : Nat) (inside : index < count) :
    (pointerCell start index).toNat = start + 8 * index :=
  MemoryRegion.address_number ⟨start, 8 * count⟩ array.valid (8 * index) (by change 8 * index ≤ 8 * count; omega)

theorem PointerArray.cell_mapped {memory : WordWrites.Memory} {width start count floor : Nat} {pointers : Nat → BitVec 64}
    (array : PointerArray memory width start count floor pointers) (index : Nat) (inside : index < count) : InitE.ordinaryDomain (pointerCell start index) := by
  apply BackingLayout.ordinary_mapped
  · rw [array.cell_number index inside]; have lower := array.valid.lower; change 2701131776 ≤ start at lower; omega
  · rw [array.cell_number index inside]; have upper := array.valid.upper; change start + 8 * count ≤ 33806089496 at upper; omega
  · rw [array.cell_number index inside]; have aligned := array.valid.aligned; change start % 8 = 0 at aligned; simp [Nat.add_mod, Nat.mul_mod, aligned]

/-- A real mutation preserving every earlier word retains the pointer
array's exact contents; later loop iterations read the same actual pointers. -/
theorem PointerArray.of_protected {source target : WordWrites.Memory} {width start count floor : Nat} {pointers : Nat → BitVec 64}
    (array : PointerArray source width start count floor pointers)
    (frame : ∀ address : BitVec 64, address.toNat < floor → target address = source address) :
    PointerArray target width start count floor pointers := by
  refine ⟨array.valid, array.earlier, ?_, array.fits, array.mapped⟩
  intro index inside
  have earlier : (pointerCell start index).toNat < floor := by rw [array.cell_number index inside]; have before := array.earlier; omega
  rw [frame _ earlier]
  exact array.words index inside

theorem PointerArray.floor_mono {memory : WordWrites.Memory} {width start count floor : Nat} {pointers : Nat → BitVec 64}
    (array : PointerArray memory width start count floor pointers) (next : Nat) (forward : floor ≤ next) :
    PointerArray memory width start count next pointers :=
  ⟨array.valid, array.earlier.trans forward, array.words, array.fits, array.mapped⟩

end InitECandidate.Solver.MutableTable

#print axioms InitECandidate.Solver.MutableTable.PointerArray.cell_number
#print axioms InitECandidate.Solver.MutableTable.PointerArray.cell_mapped
#print axioms InitECandidate.Solver.MutableTable.PointerArray.of_protected

#print axioms InitECandidate.Solver.MutableTable.PointerArray.floor_mono
