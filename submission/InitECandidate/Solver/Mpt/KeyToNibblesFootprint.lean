import InitECandidate.Solver.Mpt.KeyToNibblesReady

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

def metadata {F : Type} (source : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite {source with clock := 0, memory := fun _ => .word 0#64}

/-- Everything outside the actual output backing words is retained,
including globals, code, FFI, memory domain and other source metadata. -/
structure OutputFrame {F : Type} (source post : PanSemStateFiniteExact 64 F) (out : BitVec 64) : Prop where
  fields : metadata post = metadata source
  memory : ∀ query, (∀ offset < 64, query ≠ panByteAlignHOL (width := 64) (byteAddress out offset)) → post.memory query = source.memory query

theorem OutputFrame.refl {F : Type} (source : PanSemStateFiniteExact 64 F) (out : BitVec 64) : OutputFrame source source out :=
  ⟨rfl, fun _ _ => rfl⟩

theorem OutputFrame.trans {F : Type} (source middle post : PanSemStateFiniteExact 64 F) (out : BitVec 64)
    (first : OutputFrame source middle out) (second : OutputFrame middle post out) : OutputFrame source post out :=
  ⟨second.fields.trans first.fields, fun query outside => (second.memory query outside).trans (first.memory query outside)⟩

theorem pair_other_word {F : Type} (source : PanSemStateFiniteExact 64 F) (out index query : BitVec 64) (offset : Nat) (byte : BitVec 8)
    (firstOther : query ≠ panByteAlignHOL (width := 64) (firstAddress out index offset))
    (secondOther : query ≠ panByteAlignHOL (width := 64) (secondAddress out index offset)) :
    (pairState source out index offset byte).memory query = source.memory query := by
  change ByteStore.put _ source.be (secondAddress out index offset) (low byte) query = _
  rw [ByteStore.away _ _ _ _ _ secondOther, ByteStore.away _ _ _ _ _ firstOther]

theorem Ready.byte_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (key out query : BitVec 64)
    (index written : Nat) (bytes : Nat → BitVec 8) (ready : Ready source key out index written bytes)
    (name : String) (room : index + written + 1 ≤ 32)
    (outside : ∀ offset < 64, query ≠ panByteAlignHOL (width := 64) (byteAddress out offset)) :
    (byteState source name written out (BitVec.ofNat 64 index) (bytes (index + written))).memory query = source.memory query := by
  apply pair_other_word (bind source name (BitVec.ofNat 64 (bytes (index + written)).toNat)) out (BitVec.ofNat 64 index) query written (bytes (index + written))
  · rw [(pair_addresses out index written).1]
    exact outside _ (by omega)
  · rw [(pair_addresses out index written).2]
    exact outside _ (by omega)

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_other_word
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.Ready.byte_memory
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.OutputFrame.refl
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.OutputFrame.trans
