import InitECandidate.Solver.Input.CurrentTable.Routing

namespace InitECandidate.Solver.Input.CurrentTable.Set.Splice

def valid (old : BitVec 64 → Prop) (leaf internal node : BitVec 64) : Prop := old node ∨ node = leaf ∨ node = internal
def bits (old : BitVec 64 → Nat) (leaf internal : BitVec 64) (difference : Nat) (node : BitVec 64) : Nat :=
  if node = leaf then 256 else if node = internal then difference else old node
def keys (old : BitVec 64 → KeyBits.Key) (leaf internal stopped : BitVec 64) (query : KeyBits.Key) (node : BitVec 64) : KeyBits.Key :=
  if node = leaf then query else if node = internal then old stopped else old node
def side (old : BitVec 64 → BitVec 64) (internal parent stopped child node : BitVec 64) : BitVec 64 :=
  if node = internal then child else if node = parent ∧ old node = stopped then internal else old node

/-- One branch of the old routing image, shared by left and right proofs. -/
structure Branch (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (keys : BitVec 64 → KeyBits.Key)
    (child : BitVec 64 → BitVec 64) (digit : Bool) : Prop where
  member : ∀ node,valid node → bits node < 256 → valid (child node)
  greater : ∀ node,valid node → bits node < 256 → bits node < bits (child node)
  commonPrefix : ∀ node,valid node → bits node < 256 → ∀ position,position < bits node → KeyBits.bit (keys (child node)) position = KeyBits.bit (keys node) position
  selected : ∀ node,valid node → bits node < 256 → KeyBits.bit (keys (child node)) (bits node) = digit

structure Fresh (oldValid : BitVec 64 → Prop) (oldBits : BitVec 64 → Nat) (oldKeys : BitVec 64 → KeyBits.Key)
    (leaf internal parent stopped : BitVec 64) (difference : Nat) (query : KeyBits.Key) : Prop where
  leafFresh : ¬oldValid leaf
  internalFresh : ¬oldValid internal
  distinct : leaf ≠ internal
  leafNonzero : leaf ≠ 0#64
  internalNonzero : internal ≠ 0#64
  stoppedMember : oldValid stopped
  stoppedGreater : difference < oldBits stopped
  inside : difference < 256
  parentLower : oldValid parent → oldBits parent < difference
  commonPrefix : ∀ position,position < difference → KeyBits.bit query position = KeyBits.bit (oldKeys stopped) position
  different : KeyBits.bit query difference ≠ KeyBits.bit (oldKeys stopped) difference

variable {oldValid : BitVec 64 → Prop} {oldBits : BitVec 64 → Nat} {oldKeys : BitVec 64 → KeyBits.Key}
variable {leaf internal parent stopped : BitVec 64} {difference : Nat} {query : KeyBits.Key}

theorem Fresh.old_leaf_ne (fresh : Fresh oldValid oldBits oldKeys leaf internal parent stopped difference query)
    {node : BitVec 64} (member : oldValid node) : node ≠ leaf := by intro same; subst node; exact fresh.leafFresh member
theorem Fresh.old_internal_ne (fresh : Fresh oldValid oldBits oldKeys leaf internal parent stopped difference query)
    {node : BitVec 64} (member : oldValid node) : node ≠ internal := by intro same; subst node; exact fresh.internalFresh member

theorem Fresh.old_bits (fresh : Fresh oldValid oldBits oldKeys leaf internal parent stopped difference query)
    {node : BitVec 64} (member : oldValid node) : bits oldBits leaf internal difference node = oldBits node := by
  simp only [bits,if_neg (fresh.old_leaf_ne member),if_neg (fresh.old_internal_ne member)]

theorem Fresh.old_keys (fresh : Fresh oldValid oldBits oldKeys leaf internal parent stopped difference query)
    {node : BitVec 64} (member : oldValid node) : keys oldKeys leaf internal stopped query node = oldKeys node := by
  simp only [keys,if_neg (fresh.old_leaf_ne member),if_neg (fresh.old_internal_ne member)]

/-- The earlier real lookup route transfers its genuine first mismatch
from the reached leaf to the subtree where insertion actually stopped. -/
theorem split_prefix {left right : BitVec 64 → BitVec 64} {finish : BitVec 64}
    (model : Routing oldValid oldBits left right oldKeys) (route : Route oldBits left right query stopped finish)
    (member : oldValid stopped) (first : KeyBits.First query (oldKeys finish) difference) (greater : difference < oldBits stopped)
    (inside : difference < 256) :
    (∀ position,position < difference → KeyBits.bit query position = KeyBits.bit (oldKeys stopped) position) ∧
      KeyBits.bit query difference ≠ KeyBits.bit (oldKeys stopped) difference := by
  constructor
  · intro position earlier
    exact (first.before position earlier).trans (route.prefix model member position (by omega))
  · intro same
    exact first.unequal inside (same.trans (route.prefix model member difference greater).symm)

/-- Old branch observations survive replacing the selected parent edge by
the new internal node, whose representative is the old subtree key. -/
theorem old_branch (fresh : Fresh oldValid oldBits oldKeys leaf internal parent stopped difference query)
    {oldSide : BitVec 64 → BitVec 64} {digit : Bool} (branch : Branch oldValid oldBits oldKeys oldSide digit)
    (child node : BitVec 64) (member : oldValid node) (active : oldBits node < 256) :
    let next := side oldSide internal parent stopped child node
    valid oldValid leaf internal next ∧
      bits oldBits leaf internal difference node < bits oldBits leaf internal difference next ∧
      (∀ position,position < bits oldBits leaf internal difference node →
        KeyBits.bit (keys oldKeys leaf internal stopped query next) position = KeyBits.bit (keys oldKeys leaf internal stopped query node) position) ∧
      KeyBits.bit (keys oldKeys leaf internal stopped query next) (bits oldBits leaf internal difference node) = digit := by
  dsimp only
  rw [side,if_neg (fresh.old_internal_ne member),fresh.old_bits member,fresh.old_keys member]
  by_cases replaced : node = parent ∧ oldSide node = stopped
  · rw [if_pos replaced]
    have below : oldBits node < difference := by rw [replaced.1]; exact fresh.parentLower (replaced.1 ▸ member)
    have oldPrefix := branch.commonPrefix node member active
    have oldDigit := branch.selected node member active
    rw [replaced.2] at oldPrefix oldDigit
    simp only [bits,keys,if_neg (Ne.symm fresh.distinct),if_pos rfl]
    exact ⟨Or.inr (Or.inr rfl),below,oldPrefix,oldDigit⟩
  · rw [if_neg replaced,fresh.old_bits (branch.member node member active),fresh.old_keys (branch.member node member active)]
    exact ⟨Or.inl (branch.member node member active),branch.greater node member active,branch.commonPrefix node member active,branch.selected node member active⟩

end InitECandidate.Solver.Input.CurrentTable.Set.Splice

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.Splice.split_prefix
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.Splice.old_branch
