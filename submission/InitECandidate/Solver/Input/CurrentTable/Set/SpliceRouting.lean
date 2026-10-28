import InitECandidate.Solver.Input.CurrentTable.Set.SpliceModel

namespace InitECandidate.Solver.Input.CurrentTable.Set.Splice

def choice (leaf stopped : BitVec 64) (query : KeyBits.Key) (difference : Nat) (digit : Bool) : BitVec 64 :=
  if KeyBits.bit query difference = digit then leaf else stopped

variable {oldValid : BitVec 64 → Prop} {oldBits : BitVec 64 → Nat} {oldKeys : BitVec 64 → KeyBits.Key}
variable {leaf internal parent stopped : BitVec 64} {difference : Nat} {query : KeyBits.Key}

/-- The two fresh children have the required increasing split and retain
the old subtree prefix; which child is new comes from the actual query bit. -/
theorem fresh_branch (fresh : Fresh oldValid oldBits oldKeys leaf internal parent stopped difference query) (digit : Bool) :
    let child := choice leaf stopped query difference digit
    valid oldValid leaf internal child ∧ difference < bits oldBits leaf internal difference child ∧
      (∀ position,position < difference → KeyBits.bit (keys oldKeys leaf internal stopped query child) position = KeyBits.bit (oldKeys stopped) position) ∧
      KeyBits.bit (keys oldKeys leaf internal stopped query child) difference = digit := by
  dsimp only
  by_cases selected : KeyBits.bit query difference = digit
  · rw [choice,if_pos selected]
    simp only [bits,keys,if_pos rfl]
    exact ⟨Or.inr (Or.inl rfl),fresh.inside,fresh.commonPrefix,selected⟩
  · rw [choice,if_neg selected,fresh.old_bits fresh.stoppedMember,fresh.old_keys fresh.stoppedMember]
    refine ⟨Or.inl fresh.stoppedMember,fresh.stoppedGreater,by intros; rfl,?_⟩
    have different := fresh.different
    cases q : KeyBits.bit query difference <;> cases s : KeyBits.bit (oldKeys stopped) difference <;> cases digit <;> simp_all

theorem splice_branch (fresh : Fresh oldValid oldBits oldKeys leaf internal parent stopped difference query)
    {oldSide : BitVec 64 → BitVec 64} {digit : Bool} (branch : Branch oldValid oldBits oldKeys oldSide digit) :
    Branch (valid oldValid leaf internal) (bits oldBits leaf internal difference) (keys oldKeys leaf internal stopped query)
      (side oldSide internal parent stopped (choice leaf stopped query difference digit)) digit := by
  have observations (node : BitVec 64) (member : valid oldValid leaf internal node) (active : bits oldBits leaf internal difference node < 256) :
      let next := side oldSide internal parent stopped (choice leaf stopped query difference digit) node
      valid oldValid leaf internal next ∧
        bits oldBits leaf internal difference node < bits oldBits leaf internal difference next ∧
        (∀ position,position < bits oldBits leaf internal difference node →
          KeyBits.bit (keys oldKeys leaf internal stopped query next) position = KeyBits.bit (keys oldKeys leaf internal stopped query node) position) ∧
        KeyBits.bit (keys oldKeys leaf internal stopped query next) (bits oldBits leaf internal difference node) = digit := by
    rcases member with old | rfl | rfl
    · exact old_branch fresh branch _ node old (by rw [fresh.old_bits old] at active; exact active)
    · simp [bits] at active
    · dsimp only
      rw [side,if_pos rfl]
      simp only [bits,keys,if_neg (Ne.symm fresh.distinct),if_pos rfl]
      exact fresh_branch fresh digit
  exact ⟨fun node member active => (observations node member active).1,
    fun node member active => (observations node member active).2.1,
    fun node member active => (observations node member active).2.2.1,
    fun node member active => (observations node member active).2.2.2⟩

/-- Pure routing preservation for the exact two-node Patricia splice.
The actual stores must still establish this graph in physical memory. -/
theorem routing {left right : BitVec 64 → BitVec 64}
    (old : Routing oldValid oldBits left right oldKeys)
    (fresh : Fresh oldValid oldBits oldKeys leaf internal parent stopped difference query) :
    Routing (valid oldValid leaf internal) (bits oldBits leaf internal difference)
      (side left internal parent stopped (choice leaf stopped query difference false))
      (side right internal parent stopped (choice leaf stopped query difference true))
      (keys oldKeys leaf internal stopped query) := by
  have leftBranch : Branch oldValid oldBits oldKeys left false := ⟨old.leftMember,old.leftGreater,old.leftPrefix,old.leftDigit⟩
  have rightBranch : Branch oldValid oldBits oldKeys right true := ⟨old.rightMember,old.rightGreater,old.rightPrefix,old.rightDigit⟩
  have nextLeft := splice_branch fresh leftBranch
  have nextRight := splice_branch fresh rightBranch
  refine ⟨?_,nextLeft.member,nextRight.member,nextLeft.greater,nextRight.greater,nextLeft.commonPrefix,nextRight.commonPrefix,nextLeft.selected,nextRight.selected⟩
  intro node member
  rcases member with live | rfl | rfl
  · exact old.nonzero node live
  · exact fresh.leafNonzero
  · exact fresh.internalNonzero

end InitECandidate.Solver.Input.CurrentTable.Set.Splice

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.Splice.fresh_branch
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.Splice.routing
