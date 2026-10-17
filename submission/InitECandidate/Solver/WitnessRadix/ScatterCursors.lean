import InitECandidate.Solver.WitnessRadix.ScatterResult

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem state_zero {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat)
    (input : List (BitVec 64)) (index zero one : Nat)
    (initial : source.locals.lookup (ofString "zero_cursor") = some (.val (.word (BitVec.ofNat 64 zero)))) :
    (scatterState source dst keyFor position input index zero one).locals.lookup (ofString "zero_cursor") =
      some (.val (.word (BitVec.ofNat 64 (zero + zeros keyFor position input)))) := by
  induction input generalizing source index zero one with
  | nil => simpa only [scatterState, zeros, List.filter_nil, List.length_nil, Nat.add_zero] using initial
  | cons ordinal rest ih =>
      let selected := keep keyFor position ordinal
      let next := post (decClockHOLFinite source) dst (flagWord selected) ordinal
        (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
      have immediate := post_zero (decClockHOLFinite source) dst (flagWord selected) ordinal
        (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index) initial
      have zero' : next.locals.lookup (ofString "zero_cursor") =
          some (.val (.word (BitVec.ofNat 64 (zeroAdvance zero selected)))) := by
        cases bit : selected <;> simpa [next, flagWord, bit, zeroAdvance, BitVec.ofNat_add] using immediate
      have result := ih next (index + 1) (zeroAdvance zero selected) (oneAdvance one selected) zero'
      cases bit : keep keyFor position ordinal <;>
        simpa [scatterState, next, selected, zeros, List.filter_cons, bit, zeroAdvance,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

theorem state_one {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat)
    (input : List (BitVec 64)) (index zero one : Nat)
    (initial : source.locals.lookup (ofString "one_cursor") = some (.val (.word (BitVec.ofNat 64 one)))) :
    (scatterState source dst keyFor position input index zero one).locals.lookup (ofString "one_cursor") =
      some (.val (.word (BitVec.ofNat 64 (one + ones keyFor position input)))) := by
  induction input generalizing source index zero one with
  | nil => simpa only [scatterState, ones, List.filter_nil, List.length_nil, Nat.add_zero] using initial
  | cons ordinal rest ih =>
      let selected := keep keyFor position ordinal
      let next := post (decClockHOLFinite source) dst (flagWord selected) ordinal
        (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
      have immediate := post_one (decClockHOLFinite source) dst (flagWord selected) ordinal
        (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index) initial
      have one' : next.locals.lookup (ofString "one_cursor") =
          some (.val (.word (BitVec.ofNat 64 (oneAdvance one selected)))) := by
        cases bit : selected <;> simpa [next, flagWord, bit, oneAdvance, BitVec.ofNat_add] using immediate
      have result := ih next (index + 1) (zeroAdvance zero selected) (oneAdvance one selected) one'
      cases bit : keep keyFor position ordinal <;>
        simpa [scatterState, next, selected, ones, List.filter_cons, bit, oneAdvance,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.state_zero
#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.state_one
