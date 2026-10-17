import InitECandidate.Solver.WitnessRadix.WordBits

/-! Address-level representation of the immutable index. The read-only lookup
below follows the candidate's exact tag, shift, child and record addresses.
This is an intermediate relation: constructing it from actual stores and
lifting the traversal into Pancake HOL remain separate obligations. -/
namespace InitECandidate.Solver.WitnessRadix.Graph
open WordBits

abbrev Slice := BitVec 64 × BitVec 64
abbrev Tree := CompactIndex ByteKeys.Key Slice

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

structure Memory where
  word : BitVec 64 → BitVec 64
  byte : BitVec 64 → BitVec 8

def storedKey (memory : Memory) (keys ordinal : BitVec 64) : ByteKeys.Key :=
  ByteKeys.keyAt memory.byte (keys + ordinal * 32#64)

def storedSlice (memory : Memory) (vals ordinal : BitVec 64) : Slice :=
  let record := memory.word (vals + ordinal * 8#64)
  (memory.word record, memory.word (record + 8#64))

def Represents (memory : Memory) (keys vals : BitVec 64) : BitVec 64 → Tree → Prop
  | root, .empty => root = 0#64
  | root, .leaf key value =>
      ∃ ordinal : Nat, ordinal < 2 ^ 63 ∧ root = leafTag ordinal ∧
        storedKey memory keys (BitVec.ofNat 64 ordinal) = key ∧
        storedSlice memory vals (BitVec.ofNat 64 ordinal) = value
  | root, .branch position zero one =>
      root ≠ 0#64 ∧ root &&& 1#64 = 0#64 ∧ position < 256 ∧
        memory.word root = BitVec.ofNat 64 position ∧
        Represents memory keys vals (memory.word (root + 8#64)) zero ∧
        Represents memory keys vals (memory.word (root + 16#64)) one

/-- Outer `none` is exhausted traversal fuel; `some none` is absent. -/
noncomputable def lookup (memory : Memory) (keys vals query : BitVec 64) :
    Nat → BitVec 64 → Option (Option Slice)
  | 0, _ => none
  | fuel + 1, root =>
      if root = 0#64 then some none
      else if root &&& 1#64 ≠ 0#64 then
        let ordinal := root >>> 1
        if storedKey memory keys ordinal = ByteKeys.keyAt memory.byte query then
          some (some (storedSlice memory vals ordinal))
        else some none
      else
        let position := memory.word root
        let selected := digit (memory.byte (query + (position >>> 3))) position
        lookup memory keys vals query fuel
          (memory.word (root + if selected = 0#64 then 8#64 else 16#64))

theorem lookup_represents (memory : Memory) (keys vals query root : BitVec 64)
    (tree : Tree) (rep : Represents memory keys vals root tree)
    (fuel : Nat) (enough : compactHeight tree < fuel) :
    lookup memory keys vals query fuel root =
      some (fastLookup ByteKeys.bit (ByteKeys.keyAt memory.byte query) tree) := by
  classical
  induction tree generalizing root fuel with
  | empty =>
      change root = 0#64 at rep
      subst root
      cases fuel with
      | zero => simp [compactHeight] at enough
      | succ fuel => simp [lookup, fastLookup]
  | leaf key value =>
      obtain ⟨ordinal, small, rfl, keyEq, valueEq⟩ := rep
      cases fuel with
      | zero => simp [compactHeight] at enough
      | succ fuel =>
          by_cases equal : key = ByteKeys.keyAt memory.byte query
          all_goals simp [lookup, leafTag_nonzero ordinal small,
            leafTag_odd ordinal small, leafTag_decode ordinal small,
            keyEq, valueEq, fastLookup, equal]
  | branch position zero one ihZero ihOne =>
      obtain ⟨nonzero, even, inside, bitEq, repZero, repOne⟩ := rep
      cases fuel with
      | zero => simp [compactHeight] at enough
      | succ fuel =>
          have encoded : (BitVec.ofNat 64 position).toNat = position := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have digitEq := implementation_bit memory.byte query (BitVec.ofNat 64 position)
            (by rw [encoded]; exact inside)
          rw [encoded] at digitEq
          simp only [lookup, nonzero, even, ne_eq, not_true_eq_false, ↓reduceIte, bitEq, digitEq]
          have zeroFuel : compactHeight zero < fuel := by
            simp only [compactHeight] at enough
            omega
          have oneFuel : compactHeight one < fuel := by
            simp only [compactHeight] at enough
            omega
          cases selected : ByteKeys.bit (ByteKeys.keyAt memory.byte query) position with
          | false =>
              simpa [selected, fastLookup] using ihZero _ repZero fuel zeroFuel
          | true =>
              simpa [selected, fastLookup] using ihOne _ repOne fuel oneFuel

/-- An encoded tree built from arbitrary byte keys answers every query within
257 inspections, with duplicates resolved by the last source record. -/
theorem lookup_built (memory : Memory) (keys vals query root : BitVec 64)
    (input : List (ByteKeys.Key × Slice))
    (rep : Represents memory keys vals root (buildIndex ByteKeys.bit 256 input)) :
    lookup memory keys vals query 257 root =
      some (lastValue (ByteKeys.keyAt memory.byte query) input) := by
  classical
  rw [lookup_represents memory keys vals query root _ rep 257]
  · rw [ByteKeys.lookup]
  · have treeHeight := compactHeight_le (build ByteKeys.bit 0 256 input)
    have depth := height_build ByteKeys.bit 0 256 input
    change compactHeight (compact (build ByteKeys.bit 0 256 input)) < 257
    omega

end InitECandidate.Solver.WitnessRadix.Graph

#print axioms InitECandidate.Solver.WitnessRadix.Graph.lookup_represents
#print axioms InitECandidate.Solver.WitnessRadix.Graph.lookup_built
