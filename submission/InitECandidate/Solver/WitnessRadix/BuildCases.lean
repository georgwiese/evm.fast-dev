import InitECandidate.Solver.WitnessRadix.BuildEquations

namespace InitECandidate.Solver.WitnessRadix.BuildEquations
open InitECandidate.Solver.WitnessRadix

variable {Key Value : Type} [DecidableEq Key]

theorem lastValue_of_last (input : List (Key × Value)) (entry : Key × Value)
    (last : input.getLast? = some entry) : lastValue entry.1 input = some entry.2 := by
  induction input with
  | nil => simp at last
  | cons head rest ih =>
      cases rest with
      | nil =>
          have same : head = entry := by simpa using last
          subst head
          simp [lastValue]
      | cons next tail =>
          have tailLast : (next :: tail).getLast? = some entry := by simpa using last
          rw [lastValue, ih tailLast]

theorem build_empty_iff (bit : Key → Nat → Bool) (position fuel : Nat) (input : List (Key × Value)) :
    build bit position fuel input = .empty ↔ input = [] := by
  constructor
  · intro empty
    cases last : input.getLast? with
    | none => exact List.getLast?_eq_none_iff.mp last
    | some entry =>
        have queried := lookup_build bit entry.1 position fuel input
        rw [empty, lookup, lastValue_of_last input entry last] at queried
        cases queried
  · intro empty
    subst input
    cases fuel <;> rfl

theorem treeAt_empty_iff (bit : Key → Nat → Bool) (position fuel : Nat) (input : List (Key × Value)) :
    treeAt bit position fuel input = .empty ↔ input = [] := by
  exact (compact_empty_iff _ (rootValid_build bit position fuel input)).trans
    (build_empty_iff bit position fuel input)

theorem terminal (bit : Key → Nat → Bool) (position : Nat) (input : List (Key × Value))
    (entry : Key × Value) (last : input.getLast? = some entry) :
    treeAt bit position 0 input = .leaf entry.1 entry.2 := by
  cases input with
  | nil => simp at last
  | cons head rest => simp [treeAt, build, compact, last]

theorem unary_zero (bit : Key → Nat → Bool) (position fuel : Nat) (input : List (Key × Value))
    (empty : (input.filter fun entry => bit entry.1 position) = []) :
    treeAt bit position (fuel + 1) input = treeAt bit (position + 1) fuel input := by
  have complement : (input.filter fun entry => !bit entry.1 position) = input := by
    apply complementary_empty (fun entry => !bit entry.1 position) input
    simpa only [Bool.not_not] using empty
  rw [step, empty, complement, empty_tree, compactJoin_empty_right]

theorem split (bit : Key → Nat → Bool) (position fuel : Nat) (input : List (Key × Value))
    (zeroPresent : (input.filter fun entry => !bit entry.1 position) ≠ [])
    (onePresent : (input.filter fun entry => bit entry.1 position) ≠ []) :
    treeAt bit position (fuel + 1) input = .branch position
      (treeAt bit (position + 1) fuel (input.filter fun entry => !bit entry.1 position))
      (treeAt bit (position + 1) fuel (input.filter fun entry => bit entry.1 position)) := by
  have zeroTree : treeAt bit (position + 1) fuel (input.filter fun entry => !bit entry.1 position) ≠ .empty := by
    intro empty
    exact zeroPresent ((treeAt_empty_iff _ _ _ _).mp empty)
  have oneTree : treeAt bit (position + 1) fuel (input.filter fun entry => bit entry.1 position) ≠ .empty := by
    intro empty
    exact onePresent ((treeAt_empty_iff _ _ _ _).mp empty)
  rw [step]
  generalize left : treeAt bit (position + 1) fuel (input.filter fun entry => !bit entry.1 position) = zero
  generalize right : treeAt bit (position + 1) fuel (input.filter fun entry => bit entry.1 position) = one
  rw [left] at zeroTree
  rw [right] at oneTree
  cases zero <;> cases one <;> simp_all [compactJoin]

end InitECandidate.Solver.WitnessRadix.BuildEquations

#print axioms InitECandidate.Solver.WitnessRadix.BuildEquations.treeAt_empty_iff
#print axioms InitECandidate.Solver.WitnessRadix.BuildEquations.terminal
#print axioms InitECandidate.Solver.WitnessRadix.BuildEquations.split
