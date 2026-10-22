import InitECandidate.Solver.Mpt.KeyToNibblesMemory
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current state during the original key conversion with at most32 input bytes. `written`
counts byte pairs already written in this literal four-byte block. -/
structure SmallReady {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (length index written : Nat) (bytes : Nat → BitVec 8) : Prop where
  keyCell : source.locals.lookup (ofString "key") = some (.val (.word key))
  outCell : source.locals.lookup (ofString "out") = some (.val (.word out))
  indexCell : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))
  lengthCell : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))
  little : source.be = false
  inside : index + written ≤ length
  small : length ≤ 32
  fits : out.toNat + 64 < 2^64
  mapped : ∀ offset < 2*length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset))
  input : ByteRegion.Reads source key length bytes
  separate : ∀ left < length, ∀ right < 2*length, byteAddress key left ≠ byteAddress out right
  nibbles : NibblePrefix source out (2 * (index + written))

theorem SmallReady.byte {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (length index written : Nat) (bytes : Nat → BitVec 8) (ready : SmallReady source key out length index written bytes)
    (name : String) (notKey : ofString name ≠ ofString "key") (notOut : ofString name ≠ ofString "out")
    (notIndex : ofString name ≠ ofString "i") (notLength : ofString name ≠ ofString "n")
    (room : index + written + 1 ≤ length) :
    SmallReady (byteState source name written out (BitVec.ofNat 64 index) (bytes (index + written))) key out length index (written + 1) bytes := by
  let bound := bind source name (BitVec.ofNat 64 (bytes (index + written)).toNat)
  have firstAddressEq := (pair_addresses out index written).1
  have secondAddressEq := (pair_addresses out index written).2
  have firstMapped : bound.memaddrs (panByteAlignHOL (width := 64) (firstAddress out (BitVec.ofNat 64 index) written)) := by
    rw [firstAddressEq]
    exact ready.mapped _ (by omega)
  have secondMapped : bound.memaddrs (panByteAlignHOL (width := 64) (secondAddress out (BitVec.ofNat 64 index) written)) := by
    rw [secondAddressEq]
    exact ready.mapped _ (by omega)
  have firstOther : ∀ position < length, firstAddress out (BitVec.ofNat 64 index) written ≠ byteAddress key position := by
    intro position inside
    rw [firstAddressEq]
    exact Ne.symm (ready.separate position inside _ (by omega))
  have secondOther : ∀ position < length, secondAddress out (BitVec.ofNat 64 index) written ≠ byteAddress key position := by
    intro position inside
    rw [secondAddressEq]
    exact Ne.symm (ready.separate position inside _ (by omega))
  have input := pair_preserves_input bound key out (BitVec.ofNat 64 index) length written (bytes (index + written)) bytes
    ready.little ready.input firstOther secondOther
  have limit := ready.small
  have nibbles := NibblePrefix.pair bound out index written (bytes (index + written)) ready.little ready.fits (by omega)
    ready.nibbles firstMapped secondMapped
  have count : 2 * (index + written) + 2 = 2 * (index + (written + 1)) := by omega
  rw [count] at nibbles
  refine ⟨?_, ?_, ?_, ?_, ready.little, by omega, ready.small, ready.fits, ready.mapped, input, ready.separate, nibbles⟩
  · exact (bind_lookup_other source name "key" _ notKey).trans ready.keyCell
  · exact (bind_lookup_other source name "out" _ notOut).trans ready.outCell
  · exact (bind_lookup_other source name "i" _ notIndex).trans ready.indexCell
  · exact (bind_lookup_other source name "n" _ notLength).trans ready.lengthCell

theorem SmallReady.input_byte {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (length index written : Nat) (bytes : Nat → BitVec 8) (ready : SmallReady source key out length index written bytes)
    (room : index + written < length) :
    ByteRegion.read source (key + BitVec.ofNat 64 index + BitVec.ofNat 64 written) = some (bytes (index + written)) := by
  have read := ready.input (index + written) room
  simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using read

theorem SmallReady.restore {F : Type} (saved source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (length index written : Nat) (bytes : Nat → BitVec 8) (ready : SmallReady source key out length index written bytes)
    (name : String) (notKey : ofString "key" ≠ ofString name) (notOut : ofString "out" ≠ ofString name)
    (notIndex : ofString "i" ≠ ofString name) (notLength : ofString "n" ≠ ofString name) :
    SmallReady (restore saved name source) key out length index written bytes := by
  refine ⟨?_, ?_, ?_, ?_, ready.little, ready.inside, ready.small, ready.fits, ready.mapped, ready.input, ready.separate, ready.nibbles⟩
  · exact (restore_lookup_other saved source name "key" notKey).trans ready.keyCell
  · exact (restore_lookup_other saved source name "out" notOut).trans ready.outCell
  · exact (restore_lookup_other saved source name "i" notIndex).trans ready.indexCell
  · exact (restore_lookup_other saved source name "n" notLength).trans ready.lengthCell

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SmallReady.byte
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SmallReady.input_byte
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SmallReady.restore
