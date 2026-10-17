import InitECandidate.Solver.WitnessRadix.Keccak256BufferAgreement
import InitECandidate.Solver.WitnessRadix.Keccak256Allocated

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack PanSemStateFiniteExact AllocatedBytes

/-- The raw and aligned cells read for an ordinary buffer precede a later
allocation boundary. An empty extent makes no memory-read demand. -/
theorem buffer_cells_below (pointer : BitVec 64) (length boundary : Nat)
    (arena : Arena pointer length) (before : pointer.toNat+length≤boundary) :
    ∀ offset<length,(byteAddress pointer offset).toNat<boundary ∧
      (panByteAlignHOL (width:=64) (byteAddress pointer offset)).toNat<boundary := by
  intro offset inside
  have address:=byteAddress_toNat pointer offset (by have:=arena.upper;omega)
  constructor
  · rw [address];omega
  · rw [aligned_number,address];omega

/-- A prefix ending before private tables contains exactly the raw/aligned
hash-buffer accesses needed by the paired Keccak theorem. -/
theorem buffer_region_below (stp pointer pad out : BitVec 64) (length boundary : Nat)
    (buffers : Buffers stp pointer pad out length)
    (before : stp.toNat+200≤boundary ∧ pointer.toNat+length≤boundary ∧
      pad.toNat+136≤boundary ∧ out.toNat+32≤boundary) :
    BufferRegion (fun query=>query.toNat<boundary) stp pointer pad out length :=
  ⟨buffer_cells_below stp 200 boundary buffers.stateArena before.1,
   buffer_cells_below pointer length boundary buffers.inputArena before.2.1,
   buffer_cells_below pad 136 boundary buffers.scratchArena before.2.2.1,
   buffer_cells_below out 32 boundary buffers.outputArena before.2.2.2⟩

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.buffer_cells_below
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.buffer_region_below
