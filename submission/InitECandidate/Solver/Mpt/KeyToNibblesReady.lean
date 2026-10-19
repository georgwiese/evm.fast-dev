import InitECandidate.Solver.Mpt.KeyToNibblesMemory
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current state during the original 32-byte key conversion. `written`
counts byte pairs already written in this literal four-byte block. -/
structure Ready {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (index written : Nat) (bytes : Nat → BitVec 8) : Prop where
  keyCell : source.locals.lookup (ofString "key") = some (.val (.word key))
  outCell : source.locals.lookup (ofString "out") = some (.val (.word out))
  indexCell : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))
  lengthCell : source.locals.lookup (ofString "n") = some (.val (.word 32#64))
  little : source.be = false
  inside : index + written ≤ 32
  fits : out.toNat + 64 < 2^64
  mapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset))
  input : ByteRegion.Reads source key 32 bytes
  separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right
  nibbles : NibblePrefix source out (2 * (index + written))

theorem Ready.byte {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (index written : Nat) (bytes : Nat → BitVec 8) (ready : Ready source key out index written bytes)
    (name : String) (notKey : ofString name ≠ ofString "key") (notOut : ofString name ≠ ofString "out")
    (notIndex : ofString name ≠ ofString "i") (notLength : ofString name ≠ ofString "n")
    (room : index + written + 1 ≤ 32) :
    Ready (byteState source name written out (BitVec.ofNat 64 index) (bytes (index + written))) key out index (written + 1) bytes := by
  let bound := bind source name (BitVec.ofNat 64 (bytes (index + written)).toNat)
  have firstAddressEq := (pair_addresses out index written).1
  have secondAddressEq := (pair_addresses out index written).2
  have firstMapped : bound.memaddrs (panByteAlignHOL (width := 64) (firstAddress out (BitVec.ofNat 64 index) written)) := by
    rw [firstAddressEq]
    exact ready.mapped _ (by omega)
  have secondMapped : bound.memaddrs (panByteAlignHOL (width := 64) (secondAddress out (BitVec.ofNat 64 index) written)) := by
    rw [secondAddressEq]
    exact ready.mapped _ (by omega)
  have firstOther : ∀ position < 32, firstAddress out (BitVec.ofNat 64 index) written ≠ byteAddress key position := by
    intro position inside
    rw [firstAddressEq]
    exact Ne.symm (ready.separate position inside _ (by omega))
  have secondOther : ∀ position < 32, secondAddress out (BitVec.ofNat 64 index) written ≠ byteAddress key position := by
    intro position inside
    rw [secondAddressEq]
    exact Ne.symm (ready.separate position inside _ (by omega))
  have input := pair_preserves_input bound key out (BitVec.ofNat 64 index) 32 written (bytes (index + written)) bytes
    ready.little ready.input firstOther secondOther
  have nibbles := NibblePrefix.pair bound out index written (bytes (index + written)) ready.little ready.fits (by omega)
    ready.nibbles firstMapped secondMapped
  have count : 2 * (index + written) + 2 = 2 * (index + (written + 1)) := by omega
  rw [count] at nibbles
  refine ⟨?_, ?_, ?_, ?_, ready.little, by omega, ready.fits, ready.mapped, input, ready.separate, nibbles⟩
  · exact (bind_lookup_other source name "key" _ notKey).trans ready.keyCell
  · exact (bind_lookup_other source name "out" _ notOut).trans ready.outCell
  · exact (bind_lookup_other source name "i" _ notIndex).trans ready.indexCell
  · exact (bind_lookup_other source name "n" _ notLength).trans ready.lengthCell

theorem Ready.input_byte {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (index written : Nat) (bytes : Nat → BitVec 8) (ready : Ready source key out index written bytes)
    (room : index + written < 32) :
    ByteRegion.read source (key + BitVec.ofNat 64 index + BitVec.ofNat 64 written) = some (bytes (index + written)) := by
  have read := ready.input (index + written) room
  simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using read

theorem Ready.restore {F : Type} (saved source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (index written : Nat) (bytes : Nat → BitVec 8) (ready : Ready source key out index written bytes)
    (name : String) (notKey : ofString "key" ≠ ofString name) (notOut : ofString "out" ≠ ofString name)
    (notIndex : ofString "i" ≠ ofString name) (notLength : ofString "n" ≠ ofString name) :
    Ready (restore saved name source) key out index written bytes := by
  refine ⟨?_, ?_, ?_, ?_, ready.little, ready.inside, ready.fits, ready.mapped, ready.input, ready.separate, ready.nibbles⟩
  · exact (restore_lookup_other saved source name "key" notKey).trans ready.keyCell
  · exact (restore_lookup_other saved source name "out" notOut).trans ready.outCell
  · exact (restore_lookup_other saved source name "i" notIndex).trans ready.indexCell
  · exact (restore_lookup_other saved source name "n" notLength).trans ready.lengthCell

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.Ready.byte
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.Ready.input_byte
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.Ready.restore
