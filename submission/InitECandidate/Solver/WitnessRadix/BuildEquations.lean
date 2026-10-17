import InitECandidate.Solver.WitnessRadix.Compact

namespace InitECandidate.Solver.WitnessRadix.BuildEquations
open InitECandidate.Solver.WitnessRadix

variable {Key Value : Type} [DecidableEq Key]

def RootValid : Index Key Value → Prop
  | .bucket input => input ≠ []
  | _ => True

theorem rootValid_join (position : Nat) (left right : Index Key Value)
    (leftValid : RootValid left) (rightValid : RootValid right) : RootValid (join position left right) := by
  cases left <;> cases right <;> first | exact leftValid | exact rightValid | trivial

theorem rootValid_build (bit : Key → Nat → Bool) (position fuel : Nat) (input : List (Key × Value)) :
    RootValid (build bit position fuel input) := by
  induction fuel generalizing position input with
  | zero => cases input <;> simp [build, RootValid]
  | succ fuel ih =>
      cases input with
      | nil => trivial
      | cons entry rest =>
          apply rootValid_join
          · exact ih _ _
          · exact ih _ _

def compactJoin (position : Nat) : CompactIndex Key Value → CompactIndex Key Value → CompactIndex Key Value
  | .empty, right => right
  | left, .empty => left
  | left, right => .branch position left right

theorem compactJoin_empty_right (position : Nat) (tree : CompactIndex Key Value) :
    compactJoin position tree .empty = tree := by cases tree <;> rfl

theorem compactJoin_empty_iff (position : Nat) (left right : CompactIndex Key Value) :
    compactJoin position left right = .empty ↔ left = .empty ∧ right = .empty := by
  cases left <;> cases right <;> simp [compactJoin]

theorem compact_empty_iff (tree : Index Key Value) (valid : RootValid tree) :
    compact tree = .empty ↔ tree = .empty := by
  cases tree with
  | empty => simp [compact]
  | branch position left right => simp [compact]
  | bucket input =>
      cases last : input.getLast? with
      | none =>
          have empty : input = [] := List.getLast?_eq_none_iff.mp last
          exact False.elim (valid empty)
      | some entry => cases entry; simp [compact, last]

theorem compact_join (position : Nat) (left right : Index Key Value)
    (leftValid : RootValid left) (rightValid : RootValid right) :
    compact (join position left right) = compactJoin position (compact left) (compact right) := by
  by_cases leftEmpty : left = .empty
  · subst left
    rfl
  · by_cases rightEmpty : right = .empty
    · subst right
      have joined : join position left .empty = left := by cases left <;> rfl
      rw [joined, compact, compactJoin_empty_right]
    · have compactLeft : compact left ≠ .empty := by
        intro empty
        exact leftEmpty ((compact_empty_iff left leftValid).mp empty)
      have compactRight : compact right ≠ .empty := by
        intro empty
        exact rightEmpty ((compact_empty_iff right rightValid).mp empty)
      have joined : join position left right = .branch position left right := by
        cases left <;> cases right <;> simp_all [join]
      rw [joined, compact]
      cases l : compact left <;> cases r : compact right <;>
        simp_all [compactJoin]

def treeAt (bit : Key → Nat → Bool) (position fuel : Nat) (input : List (Key × Value)) :
    CompactIndex Key Value := compact (build bit position fuel input)

theorem empty_tree (bit : Key → Nat → Bool) (position fuel : Nat) :
    treeAt bit position fuel ([] : List (Key × Value)) = .empty := by
  cases fuel <;> rfl

theorem step (bit : Key → Nat → Bool) (position fuel : Nat) (input : List (Key × Value)) :
    treeAt bit position (fuel + 1) input = compactJoin position
      (treeAt bit (position + 1) fuel (input.filter fun entry => !bit entry.1 position))
      (treeAt bit (position + 1) fuel (input.filter fun entry => bit entry.1 position)) := by
  cases input with
  | nil => simp only [List.filter_nil, empty_tree, compactJoin]
  | cons entry rest =>
      exact compact_join position _ _ (rootValid_build bit _ _ _) (rootValid_build bit _ _ _)

theorem singleton (bit : Key → Nat → Bool) (position fuel : Nat) (entry : Key × Value) :
    treeAt bit position fuel [entry] = .leaf entry.1 entry.2 := by
  induction fuel generalizing position with
  | zero => rfl
  | succ fuel ih =>
      rw [step]
      cases selected : bit entry.1 position <;>
        simp [List.filter_cons, selected, empty_tree, ih, compactJoin]

theorem complementary_empty {Entry : Type} (keep : Entry → Bool) (input : List Entry)
    (empty : (input.filter fun entry => !keep entry) = []) : input.filter keep = input := by
  induction input with
  | nil => rfl
  | cons entry rest ih =>
      cases selected : keep entry with
      | false => simp [List.filter_cons, selected] at empty
      | true =>
          simp only [List.filter_cons, selected, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at empty ⊢
          rw [ih empty]

theorem unary_one (bit : Key → Nat → Bool) (position fuel : Nat) (input : List (Key × Value))
    (empty : (input.filter fun entry => !bit entry.1 position) = []) :
    treeAt bit position (fuel + 1) input = treeAt bit (position + 1) fuel input := by
  rw [step, empty, complementary_empty _ input empty]
  rw [empty_tree]
  rfl

end InitECandidate.Solver.WitnessRadix.BuildEquations

#print axioms InitECandidate.Solver.WitnessRadix.BuildEquations.step
#print axioms InitECandidate.Solver.WitnessRadix.BuildEquations.singleton
#print axioms InitECandidate.Solver.WitnessRadix.BuildEquations.unary_one
