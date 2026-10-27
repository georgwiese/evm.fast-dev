import InitECandidate.Solver.Input.CurrentStartup.StatelessEntry
import InitECandidate.Solver.Input.NormalHeapEffects

namespace InitECandidate.Solver.Input.CurrentStartup.DecoderInput
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real copy allocation leaves the next heap beyond every copied byte
and its requested eight-byte padding. Alignment rounding only moves it up. -/
theorem copied_frontier (input : Guest.InputBlob) (before ready : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (length : Nat) (value : ValueHOL 64)
    (copied : Blob.Copied {before with clock := before.clock - 1} ready input pointer length value) :
    NormalHeapEffects.AtLeast (pointer.toNat + length + 8) ready := by
  let amount := BitVec.ofNat 64 (length + 8)
  have number : amount.toNat = length + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := copied.1; omega)]
  have guarded := WitnessRadix.PersistentAlloc.guards pointer amount (by rw [number]; exact copied.1)
  refine ⟨WitnessRadix.PersistentAlloc.rounded pointer amount, ?_, ?_, guarded.2.2.2.1, guarded.2.2.2.2⟩
  · rw [copied.2.2.2.2.1]
    simp [WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE, amount]
  · simpa only [number, Nat.add_assoc] using guarded.2.2.1

end InitECandidate.Solver.Input.CurrentStartup.DecoderInput

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.copied_frontier
