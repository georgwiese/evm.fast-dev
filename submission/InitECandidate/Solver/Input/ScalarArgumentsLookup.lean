import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Successful original scalar ABIs derive argument types even when the
caller expressions are arbitrary failed or ill-typed memory/global reads. -/
theorem two_scalar_words (code : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function first second : MlS) (body actual : ProgHOL 64) (shape actualShape : ShapeHOL)
    (entry : code function=some ([(first,.one),(second,.one)],body,shape))
    (left right : ValueHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (called : lookupCodeHOLFinite code function [left,right]=some (actual,callee,actualShape)) :
    ∃ a b : BitVec 64,left=.val (.word a) ∧ right=.val (.word b) := by
  have raw:=lookupCodeHOLFinite_eq_some code function [left,right] actual callee actualShape called
  simp only [lookupCodeHOLExact,entry] at raw
  split at raw
  · rename_i valid
    have checks : shapeEqHOL .one (shapeOfHOLExact left)=true ∧ shapeEqHOL .one (shapeOfHOLExact right)=true:=by
      simpa using valid.2.2
    obtain ⟨a,leftEq⟩:=RlpWrite.U256Value.scalar_word left ((shapeEqHOL_eq_true _ _).mp checks.1).symm
    obtain ⟨b,rightEq⟩:=RlpWrite.U256Value.scalar_word right ((shapeEqHOL_eq_true _ _).mp checks.2).symm
    exact ⟨a,b,leftEq,rightEq⟩
  · cases raw

theorem three_scalar_words (code : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function first second third : MlS) (body actual : ProgHOL 64) (shape actualShape : ShapeHOL)
    (entry : code function=some ([(first,.one),(second,.one),(third,.one)],body,shape))
    (left middle right : ValueHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (called : lookupCodeHOLFinite code function [left,middle,right]=some (actual,callee,actualShape)) :
    ∃ a b c : BitVec 64,left=.val (.word a) ∧ middle=.val (.word b) ∧ right=.val (.word c) := by
  have raw:=lookupCodeHOLFinite_eq_some code function [left,middle,right] actual callee actualShape called
  simp only [lookupCodeHOLExact,entry] at raw
  split at raw
  · rename_i valid
    have checks : shapeEqHOL .one (shapeOfHOLExact left)=true ∧ shapeEqHOL .one (shapeOfHOLExact middle)=true ∧
        shapeEqHOL .one (shapeOfHOLExact right)=true:=by simpa using valid.2.2
    obtain ⟨a,leftEq⟩:=RlpWrite.U256Value.scalar_word left ((shapeEqHOL_eq_true _ _).mp checks.1).symm
    obtain ⟨b,middleEq⟩:=RlpWrite.U256Value.scalar_word middle ((shapeEqHOL_eq_true _ _).mp checks.2.1).symm
    obtain ⟨c,rightEq⟩:=RlpWrite.U256Value.scalar_word right ((shapeEqHOL_eq_true _ _).mp checks.2.2).symm
    exact ⟨a,b,c,leftEq,middleEq,rightEq⟩
  · cases raw

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.two_scalar_words
#print axioms InitECandidate.Solver.Input.CallNormal.three_scalar_words
