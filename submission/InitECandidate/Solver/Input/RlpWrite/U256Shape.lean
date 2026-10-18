import InitECandidate.Solver.Input.RlpWrite.U256Value

namespace InitECandidate.Solver.Input.RlpWrite.U256Value
open Flapjack Flapjack.Pancake.PanLang

theorem scalar_word (value : ValueHOL 64) (shape : shapeOfHOLExact value = .one) :
    ∃ word : BitVec 64, value = .val (.word word) := by
  cases value with
  | val payload => cases payload with | word word => exact ⟨word, rfl⟩
  | rStruct fields => simp only [shapeOfHOLExact] at shape; cases shape
  | nStruct name fields => simp only [shapeOfHOLExact] at shape; cases shape

/-- The exact source carrier has only word leaves. A genuinely checked
four-scalar shape therefore supplies four actual words, without a separate
assumption about their values or memory contents. -/
theorem of_shape (value : ValueHOL 64) (shape : shapeOfHOLExact value = tupleShape) :
    ∃ words : Words, value = tuple words := by
  cases value with
  | val payload => simp only [shapeOfHOLExact, tupleShape] at shape; cases shape
  | nStruct name fields => simp only [shapeOfHOLExact] at shape; cases shape
  | rStruct fields =>
    simp only [shapeOfHOLExact, tupleShape] at shape
    have shapes : fields.map shapeOfHOLExact = [.one, .one, .one, .one] := ShapeHOL.comb.inj shape
    have length := congrArg List.length shapes
    simp only [List.length_map] at length
    cases fields with
    | nil => simp at length
    | cons a rest =>
      cases rest with
      | nil => simp at length
      | cons b rest =>
        cases rest with
        | nil => simp at length
        | cons c rest =>
          cases rest with
          | nil => simp at length
          | cons d rest =>
            have pieces : shapeOfHOLExact a = .one ∧ shapeOfHOLExact b = .one ∧
                shapeOfHOLExact c = .one ∧ shapeOfHOLExact d = .one ∧ rest.map shapeOfHOLExact = [] := by
              simpa only [List.map_cons, List.cons.injEq] using shapes
            have empty : rest = [] := by
              cases rest with
              | nil => rfl
              | cons head tail => cases pieces.2.2.2.2
            obtain ⟨wa, rfl⟩ := scalar_word a pieces.1
            obtain ⟨wb, rfl⟩ := scalar_word b pieces.2.1
            obtain ⟨wc, rfl⟩ := scalar_word c pieces.2.2.1
            obtain ⟨wd, rfl⟩ := scalar_word d pieces.2.2.2.1
            subst rest
            exact ⟨fun index => if index.val = 0 then wa else if index.val = 1 then wb else if index.val = 2 then wc else wd, rfl⟩

end InitECandidate.Solver.Input.RlpWrite.U256Value

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Value.scalar_word
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Value.of_shape
