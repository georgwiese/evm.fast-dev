import InitECandidate.Solver.Input.CurrentTable.Set.SpliceRouting
import InitECandidate.Solver.Input.CurrentTable.Set.SeekLoop
import InitECandidate.Solver.Input.CurrentTable.ImageFacts

namespace InitECandidate.Solver.Input.CurrentTable.Set.Splice
open Flapjack PanSemStateFiniteExact

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root stopped parent finish : BitVec 64}
variable {next count difference : Nat} {oldValid : BitVec 64 → Prop} {oldBits : BitVec 64 → Nat}
variable {left right : BitVec 64 → BitVec 64} {oldKeys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop} {query : KeyBits.Key}

/-- Real table history, earlier lookup route and actual strict search exit
supply every premise of the two-fresh-node routing preservation theorem. -/
theorem fresh_from_image (image : Image source table cap root next count oldValid oldBits left right oldKeys ValueOf)
    (member : oldValid stopped) (route : Route oldBits left right query stopped finish)
    (link : ParentLink oldValid oldBits left right query root stopped parent difference)
    (first : KeyBits.First query (oldKeys finish) difference) (inside : difference < 256) (strict : difference < oldBits stopped) :
    Fresh oldValid oldBits oldKeys (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) parent stopped difference query := by
  have small := image.next_small
  have nextNumber : (BitVec.ofNat 64 next).toNat = next := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have internalNumber : (BitVec.ofNat 64 (next+1)).toNat = next+1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have split := split_prefix image.routing route member first strict inside
  refine ⟨image.fresh_next,image.fresh_next_succ,?_,?_,?_,member,strict,inside,?_,split.1,split.2⟩
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [nextNumber,internalNumber] at equal
    omega
  · intro zero
    have equal := congrArg BitVec.toNat zero
    rw [nextNumber] at equal
    have := image.nextLower
    change next = 0 at equal
    omega
  · intro zero
    have equal := congrArg BitVec.toNat zero
    rw [internalNumber] at equal
    change next+1 = 0 at equal
    omega
  · intro live
    rcases link with empty | nonempty
    · exact (image.routing.nonzero parent live empty.1).elim
    · exact nonempty.2.1

/-- The exact two fresh IDs extend the old allocated-index interval by
two, without word wrap or accidental reuse of an existing valid index. -/
theorem valid_range (image : Image source table cap root next count oldValid oldBits left right oldKeys ValueOf) (node : BitVec 64) :
    valid oldValid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) node ↔ 1 ≤ node.toNat ∧ node.toNat < next+2 := by
  have small := image.next_small
  have nextNumber : (BitVec.ofNat 64 next).toNat = next := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have internalNumber : (BitVec.ofNat 64 (next+1)).toNat = next+1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  constructor
  · intro live
    rcases live with old | rfl | rfl
    · have := (image.validRange node).mp old
      omega
    · rw [nextNumber]
      have := image.nextLower
      omega
    · rw [internalNumber]
      omega
  · intro range
    by_cases old : node.toNat < next
    · exact Or.inl ((image.validRange node).mpr ⟨range.1,old⟩)
    · by_cases first : node.toNat = next
      · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (first.trans nextNumber.symm)))
      · exact Or.inr (Or.inr (BitVec.eq_of_toNat_eq (show node.toNat = (BitVec.ofNat 64 (next+1)).toNat by rw [internalNumber]; omega)))

end InitECandidate.Solver.Input.CurrentTable.Set.Splice

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.Splice.fresh_from_image
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.Splice.valid_range
