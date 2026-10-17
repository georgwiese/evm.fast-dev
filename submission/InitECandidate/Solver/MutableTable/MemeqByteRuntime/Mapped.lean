import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Execution

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix

/-- Observed bytes of the actual source memory, with no content restriction. -/
def observed {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (offset : Nat) : UInt8 :=
  UInt8.ofBitVec (ByteRegion.value source (byteAddress pointer offset))

theorem observed_read {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (offset : Nat)
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset))) :
    @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (byteAddress pointer offset) = some (observed source pointer offset) := by
  rw [panMemLoadByteHOL_eq_word8_projection]
  have read := ByteRegion.mapped_read source (byteAddress pointer offset) mapped
  change @panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) source.be
    (byteAddress pointer offset) = some (ByteRegion.value source (byteAddress pointer offset)) at read
  rw [read]
  rfl

theorem inputs_of_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length : Nat)
    (aLocal : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "b") = some (.val (.word b)))
    (lengthLocal : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset))) :
    Inputs source a b length (observed source a) (observed source b) :=
  ⟨aLocal, bLocal, lengthLocal, (by intro offset inside; exact observed_read source a offset (leftMapped offset inside)),
    (by intro offset inside; exact observed_read source b offset (rightMapped offset inside))⟩

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.observed_read
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.inputs_of_mapped
