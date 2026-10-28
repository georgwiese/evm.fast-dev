import InitECandidate.Solver.Input.CurrentTable.Set.SpliceEntry
import InitECandidate.Solver.Input.CurrentTable.Set.FreshKeys

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Entry information to derive from the real earlier lookup/strict search
and current builder counter. No future execution or funding is included. -/
structure InsertContext (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap root pointer value node parent : BitVec 64)
    (next count difference : Nat) (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat)
    (left right : BitVec 64 → BitVec 64) (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop) : Prop where
  image : Image source table cap root next count valid bits left right keys ValueOf
  available : next+1 ≤ cap.toNat
  countRoom : count+1 ≤ cap.toNat
  fresh : Splice.Fresh valid bits keys (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) parent node difference query
  link : ParentLink valid bits left right query root node parent difference
  little : source.be = false
  aligned : pointer.toNat%8 = 0
  beforeTable : pointer.toNat+32 ≤ table.toNat
  view : FirstDiff.ByteView source pointer query
  valueMember : ValueOf value

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value node parent : BitVec 64}
variable {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key} {ValueOf : BitVec 64 → Prop}

theorem InsertContext.node_inside (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf) :
    node.toNat ≤ cap.toNat := data.image.node_inside node data.fresh.stoppedMember

theorem InsertContext.parent_inside (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf) :
    parent.toNat ≤ cap.toNat := by
  rcases data.link with empty | nonempty
  · rw [empty.1]; change 0 ≤ cap.toNat; omega
  · exact data.image.node_inside parent nonempty.1

theorem InsertContext.parent_not_leaf (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf) :
    parent ≠ BitVec.ofNat 64 next := by
  rcases data.link with empty | nonempty
  · rw [empty.1]; exact Ne.symm data.fresh.leafNonzero
  · exact data.fresh.old_leaf_ne nonempty.1

theorem InsertContext.parent_not_internal (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf) :
    parent ≠ BitVec.ofNat 64 (next+1) := by
  rcases data.link with empty | nonempty
  · rw [empty.1]; exact Ne.symm data.fresh.internalNonzero
  · exact data.fresh.old_internal_ne nonempty.1

theorem InsertContext.old_leaf_not_parent (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : valid index) (marked : bits index = 256) : index ≠ parent := by
  intro same
  rcases data.link with empty | nonempty
  · exact data.image.routing.nonzero index member (same.trans empty.1)
  · have smaller := nonempty.2.1
    have inside := data.fresh.inside
    rw [←same,marked] at smaller
    omega

theorem InsertContext.parent_edges (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (nonzero : parent ≠ 0#64) : valid parent ∧ bits parent < 256 ∧ (left parent = node ∨ right parent = node) := by
  rcases data.link with empty | nonempty
  · exact (nonzero empty.1).elim
  · refine ⟨nonempty.1,by have := data.fresh.inside; have := nonempty.2.1; omega,?_⟩
    have selected := nonempty.2.2
    cases digit : KeyBits.bit query (bits parent)
    · exact Or.inl (by simpa [digit] using selected.symm)
    · exact Or.inr (by simpa [digit] using selected.symm)

theorem InsertContext.right_selected (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (nonzero : parent ≠ 0#64) : right parent = node ↔ left parent ≠ node := by
  obtain ⟨member,active,either⟩ := data.parent_edges nonzero
  have distinct : left parent ≠ right parent := by
    intro same
    have leftDigit := data.image.routing.leftDigit parent member active
    have rightDigit := data.image.routing.rightDigit parent member active
    rw [same,rightDigit] at leftDigit
    cases leftDigit
  constructor
  · intro rightEq leftEq
    exact distinct (leftEq.trans rightEq.symm)
  · intro notLeft
    exact either.resolve_left notLeft

theorem InsertContext.valid_inside (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) index) : index.toNat ≤ cap.toNat := by
  have range := (Splice.valid_range data.image index).mp member
  have available := data.available
  omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.InsertContext.parent_edges
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.InsertContext.right_selected
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.InsertContext.valid_inside
