import InitECandidate.Solver.WitnessRadix.WordWrites
import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteReads

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A finite sequence of actual word stores protects a physical byte key
when every byte's aligned backing cell is outside its write footprint. -/
theorem word_writes_bytes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (writes : List (BitVec 64 × BitVec 64))
    (pointer : BitVec 64) (key : CurrentTable.KeyBits.Key)
    (away : ∀ entry ∈ writes,∀ byte : Fin 32,panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 byte.val) ≠ entry.1)
    (view : CurrentTable.FirstDiff.ByteView source pointer key) :
    CurrentTable.FirstDiff.ByteView {source with memory := WordWrites.write source.memory writes} pointer key := by
  induction writes generalizing source with
  | nil => exact view
  | cons entry rest ih =>
    obtain ⟨address,value⟩ := entry
    have nextView := StoreWord.byteView_away source address value pointer key (away (address,value) (by simp)) view
    exact ih {source with memory := StoreWord.put source.memory address value}
      (by intro entry member; exact away entry (List.mem_cons_of_mem _ member)) nextView

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.word_writes_bytes
