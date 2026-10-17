import InitECandidate.Solver.WitnessRadix.ScatterLoop
import InitECandidate.Solver.WitnessRadix.WordScatter

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual scatter poststate equals the stable word-memory scatter, with
exact clock consumption and preservation of all other nonlocal fields. -/
theorem state_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat)
    (input : List (BitVec 64)) (index zero one : Nat) :
    emptyLocalsHOLFinite (scatterState source dst keyFor position input index zero one) =
      emptyLocalsHOLFinite { source with
        memory := WordScatter.scatterWords (wordAddress dst) (keep keyFor position) input source.memory zero one
        clock := source.clock - input.length } := by
  induction input generalizing source index zero one with
  | nil => simp [scatterState, WordScatter.scatterWords]
  | cons ordinal rest ih =>
      let selected := keep keyFor position ordinal
      let entry := decClockHOLFinite source
      let next := post entry dst (flagWord selected) ordinal
        (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
      rw [scatterState, ih]
      have frame := post_frame entry dst (flagWord selected) ordinal (BitVec.ofNat 64 zero)
        (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
      have shifted := congrArg (fun state : PanSemStateFiniteExact 64 F =>
        { state with
          memory := WordScatter.scatterWords (wordAddress dst) (keep keyFor position) rest state.memory
            (zeroAdvance zero selected) (oneAdvance one selected)
          clock := state.clock - rest.length }) frame
      have clockSub : source.clock - 1 - rest.length = source.clock - (ordinal :: rest).length := by
        simp only [List.length_cons]
        omega
      cases bit : keep keyFor position ordinal <;>
        simpa [post, QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite, entry, decClockHOLFinite, selected, bit, flagWord,
          destination, wordAddress, zeroAdvance, oneAdvance, WordScatter.scatterWords,
          Bool.false_eq_true, ↓reduceIte, clockSub] using shifted

theorem state_other {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat)
    (input : List (BitVec 64)) (index zero one : Nat) (name : MlS)
    (notI : ofString "i" ≠ name) (notZero : ofString "zero_cursor" ≠ name)
    (notOne : ofString "one_cursor" ≠ name) :
    (scatterState source dst keyFor position input index zero one).locals.lookup name = source.locals.lookup name := by
  induction input generalizing source index zero one with
  | nil => rfl
  | cons ordinal rest ih =>
      rw [scatterState, ih, post_lookup _ _ _ _ _ _ _ name notI notZero notOne]
      rfl

theorem state_index {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat)
    (input : List (BitVec 64)) (index zero one : Nat)
    (initial : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    (scatterState source dst keyFor position input index zero one).locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 (index + input.length)))) := by
  induction input generalizing source index zero one with
  | nil => simpa only [scatterState, List.length_nil, Nat.add_zero] using initial
  | cons ordinal rest ih =>
      let selected := keep keyFor position ordinal
      let next := post (decClockHOLFinite source) dst (flagWord selected) ordinal
        (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
      have immediate := post_index (decClockHOLFinite source) dst (flagWord selected) ordinal
        (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
      have index' : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
        simpa only [← BitVec.ofNat_add] using immediate
      have result := ih next (index + 1) (zeroAdvance zero selected) (oneAdvance one selected) index'
      simpa only [scatterState, List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using result

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.state_frame
#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.state_index
