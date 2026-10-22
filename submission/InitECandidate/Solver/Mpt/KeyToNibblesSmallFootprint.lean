import InitECandidate.Solver.Mpt.KeyToNibblesSmallReady
import InitECandidate.Solver.Mpt.KeyToNibblesFootprint

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

theorem SmallReady.byte_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (key out query : BitVec 64)
    (length index written : Nat) (bytes : Nat → BitVec 8) (ready : SmallReady source key out length index written bytes)
    (name : String) (room : index + written + 1 ≤ length)
    (outside : ∀ offset < 64, query ≠ panByteAlignHOL (width := 64) (byteAddress out offset)) :
    (byteState source name written out (BitVec.ofNat 64 index) (bytes (index + written))).memory query = source.memory query := by
  apply pair_other_word (bind source name (BitVec.ofNat 64 (bytes (index + written)).toNat)) out (BitVec.ofNat 64 index) query written (bytes (index + written))
  · rw [(pair_addresses out index written).1]
    exact outside _ (by have limit:=ready.small; omega)
  · rw [(pair_addresses out index written).2]
    exact outside _ (by have limit:=ready.small; omega)

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SmallReady.byte_memory
