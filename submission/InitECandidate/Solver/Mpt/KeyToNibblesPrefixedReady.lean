import InitECandidate.Solver.Mpt.KeyToNibblesPrefixedMemory
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual converter state for long witness paths, retaining an already
written compact-path nibble before the ordinary conversion output. Byte
contents of the input may vary; only output nibble range is required. -/
structure PrefixedReady {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index written : Nat) : Prop where
  keyCell : source.locals.lookup (ofString "key")=some (.val (.word key))
  outCell : source.locals.lookup (ofString "out")=some (.val (.word (out+BitVec.ofNat 64 leading)))
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))
  little : source.be=false
  inside : index+written≤length
  small : length≤1024
  fits : out.toNat+(leading+2*length)<2^64
  mapped : ∀ offset<leading+2*length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset))
  inputMapped : ∀ offset<length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset))
  nibbles : NibblePrefix source out (leading+2*(index+written))

theorem PrefixedReady.input_byte {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index written : Nat) (ready : PrefixedReady source key out leading length index written)
    (room : index+written<length) :
    ByteRegion.read source (key+BitVec.ofNat 64 index+BitVec.ofNat 64 written)=
      some (ByteRegion.value source (key+BitVec.ofNat 64 index+BitVec.ofNat 64 written)) := by
  apply ByteRegion.mapped_read
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using ready.inputMapped (index+written) room

theorem PrefixedReady.byte {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index written : Nat) (ready : PrefixedReady source key out leading length index written)
    (name : String) (byte : BitVec 8)
    (notKey : ofString name≠ofString "key") (notOut : ofString name≠ofString "out")
    (notIndex : ofString name≠ofString "i") (notLength : ofString name≠ofString "n")
    (room : index+written+1≤length) :
    PrefixedReady (byteState source name written (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) byte)
      key out leading length index (written+1) := by
  let bound:=bind source name (BitVec.ofNat 64 byte.toNat)
  have addresses:=prefix_pair_addresses out leading index written
  have firstMapped : bound.memaddrs (panByteAlignHOL (width:=64) (firstAddress (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) written)):=by
    rw [addresses.1]
    exact ready.mapped _ (by omega)
  have secondMapped : bound.memaddrs (panByteAlignHOL (width:=64) (secondAddress (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) written)):=by
    rw [addresses.2]
    exact ready.mapped _ (by omega)
  have nibbles:=NibblePrefix.pair_prefixed bound out leading index written byte ready.little
    (by have fits:=ready.fits; omega) ready.nibbles firstMapped secondMapped
  have count : leading+2*(index+written)+2=leading+2*(index+(written+1)):=by omega
  rw [count] at nibbles
  refine ⟨?_,?_,?_,?_,ready.little,by omega,ready.small,ready.fits,ready.mapped,ready.inputMapped,nibbles⟩
  · exact (bind_lookup_other source name "key" _ notKey).trans ready.keyCell
  · exact (bind_lookup_other source name "out" _ notOut).trans ready.outCell
  · exact (bind_lookup_other source name "i" _ notIndex).trans ready.indexCell
  · exact (bind_lookup_other source name "n" _ notLength).trans ready.lengthCell

theorem PrefixedReady.restore {F : Type} (saved source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index written : Nat) (ready : PrefixedReady source key out leading length index written)
    (name : String) (notKey : ofString "key"≠ofString name) (notOut : ofString "out"≠ofString name)
    (notIndex : ofString "i"≠ofString name) (notLength : ofString "n"≠ofString name) :
    PrefixedReady (restore saved name source) key out leading length index written := by
  refine ⟨?_,?_,?_,?_,ready.little,ready.inside,ready.small,ready.fits,ready.mapped,ready.inputMapped,ready.nibbles⟩
  · exact (restore_lookup_other saved source name "key" notKey).trans ready.keyCell
  · exact (restore_lookup_other saved source name "out" notOut).trans ready.outCell
  · exact (restore_lookup_other saved source name "i" notIndex).trans ready.indexCell
  · exact (restore_lookup_other saved source name "n" notLength).trans ready.lengthCell

theorem PrefixedReady.with_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index written clock : Nat) (ready : PrefixedReady source key out leading length index written) :
    PrefixedReady {source with clock:=clock} key out leading length index written :=
  ⟨ready.keyCell,ready.outCell,ready.indexCell,ready.lengthCell,ready.little,ready.inside,ready.small,ready.fits,ready.mapped,ready.inputMapped,ready.nibbles⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.PrefixedReady.input_byte
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.PrefixedReady.byte
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.PrefixedReady.restore
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.PrefixedReady.with_clock
