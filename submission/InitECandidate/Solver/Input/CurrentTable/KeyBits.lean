import InitECandidate.Solver.PanState
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find

namespace InitECandidate.Solver.Input.CurrentTable.KeyBits

abbrev Key := Fin 32 → BitVec 8

/-- Actual current Patricia order: bytes in address order, most significant
bit first in each byte, as used by htab_first_diff and htab_find_leaf. -/
def bit (key : Key) (position : Nat) : Bool :=
  (key (Fin.ofNat 32 (position / 8))).getLsbD (7 - position % 8)

theorem byte_index (position : Nat) (inside : position < 256) :
    (Fin.ofNat 32 (position / 8)).val = position / 8 := by
  change (position / 8) % 32 = position / 8
  apply Nat.mod_eq_of_lt
  omega

/-- Agreement of the actual256bits determines every byte of a current key. -/
theorem separates (left right : Key)
    (same : ∀ position < 256, bit left position = bit right position) : left = right := by
  funext byte
  apply BitVec.eq_of_getLsbD_eq
  intro digit digitInside
  have positionInside : 8 * byte.val + (7 - digit) < 256 := by have := byte.isLt; omega
  have div : (8 * byte.val + (7 - digit)) / 8 = byte.val := by omega
  have rem : (8 * byte.val + (7 - digit)) % 8 = 7 - digit := by omega
  have index : Fin.ofNat 32 ((8 * byte.val + (7 - digit)) / 8) = byte := by
    apply Fin.ext
    rw [byte_index _ positionInside,div]
  have reversed : 7 - (7 - digit) = digit := by omega
  simpa only [bit,index,rem,reversed] using same _ positionInside

theorem mismatch_exists (left right : Key) (different : left ≠ right) :
    ∃ position,position < 256 ∧ bit left position ≠ bit right position := by
  by_contra absent
  apply different
  apply separates
  intro position inside
  by_contra unequal
  exact absent ⟨position,inside,unequal⟩

/-- The mathematical least mismatch; connecting it to the actual source
return is a separate required execution proof. Equal keys use marker256. -/
noncomputable def first (left right : Key) : Nat := by
  classical
  exact if same : left = right then 256 else Nat.find (mismatch_exists left right same)

structure First (left right : Key) (position : Nat) : Prop where
  bounded : position ≤ 256
  before : ∀ prior,prior < position → bit left prior = bit right prior
  unequal : position < 256 → bit left position ≠ bit right position

theorem first_spec (left right : Key) : First left right (first left right) := by
  classical
  unfold first
  split
  · rename_i same
    subst right
    exact ⟨by omega,by intros; rfl,by omega⟩
  · rename_i different
    have existsMismatch := mismatch_exists left right different
    have chosen := Nat.find_spec existsMismatch
    refine ⟨by omega,?_,fun _ => chosen.2⟩
    intro prior earlier
    have absent := Nat.find_min existsMismatch earlier
    by_contra unequal
    exact absent ⟨by omega,unequal⟩

theorem First.unique {left right : Key} {a b : Nat}
    (one : First left right a) (two : First left right b) : a = b := by
  by_cases smaller : a < b
  · exact False.elim (one.unequal (by have := two.bounded; omega) (two.before a smaller))
  by_cases larger : b < a
  · exact False.elim (two.unequal (by have := one.bounded; omega) (one.before b larger))
  omega

theorem First.marker_iff {left right : Key} {position : Nat} (result : First left right position) :
    position = 256 ↔ left = right := by
  constructor
  · intro marker
    apply separates
    intro prior inside
    exact result.before prior (by omega)
  · intro same
    by_contra below
    have inside : position < 256 := by have := result.bounded; omega
    exact result.unequal inside (by rw [same])

/-- Every full byte before the least differing bit agrees, in actual address
order. The selected byte has the specified most-significant-first bit. -/
theorem First.bytes_before {left right : Key} {position : Nat}
    (result : First left right position) (index : Fin 32) (earlier : index.val < position / 8) :
    left index = right index := by
  apply BitVec.eq_of_getLsbD_eq
  intro digit digitInside
  have prior : 8 * index.val + (7 - digit) < position := by omega
  have inside : 8 * index.val + (7 - digit) < 256 := by have := result.bounded; omega
  have div : (8 * index.val + (7 - digit)) / 8 = index.val := by omega
  have rem : (8 * index.val + (7 - digit)) % 8 = 7 - digit := by omega
  have selected : Fin.ofNat 32 ((8 * index.val + (7 - digit)) / 8) = index := by
    apply Fin.ext
    rw [byte_index _ inside,div]
  have reversed : 7 - (7 - digit) = digit := by omega
  simpa only [bit,selected,rem,reversed] using result.before _ prior

end InitECandidate.Solver.Input.CurrentTable.KeyBits

#print axioms InitECandidate.Solver.Input.CurrentTable.KeyBits.separates
#print axioms InitECandidate.Solver.Input.CurrentTable.KeyBits.first_spec
#print axioms InitECandidate.Solver.Input.CurrentTable.KeyBits.First.unique
#print axioms InitECandidate.Solver.Input.CurrentTable.KeyBits.First.bytes_before
