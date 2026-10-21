import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.Input.ScalarPair
open Flapjack Flapjack.Pancake.PanLang

def tupleShape : ShapeHOL := .comb [.one,.one]
def tuple (left right : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word left),.val (.word right)]

/-- An actually checked two-scalar shape contains exactly two word leaves. -/
theorem of_shape (value : ValueHOL 64) (shape : shapeOfHOLExact value=tupleShape) :
    ∃ left right : BitVec 64,value=tuple left right := by
  cases value with
  | val payload=>simp only [shapeOfHOLExact,tupleShape] at shape; cases shape
  | nStruct name fields=>simp only [shapeOfHOLExact,tupleShape] at shape; cases shape
  | rStruct fields=>
    simp only [shapeOfHOLExact,tupleShape] at shape
    have shapes : fields.map shapeOfHOLExact=[.one,.one] := ShapeHOL.comb.inj shape
    have count:=congrArg List.length shapes
    simp only [List.length_map] at count
    cases fields with
    | nil=>simp at count
    | cons left rest=>
      cases rest with
      | nil=>simp at count
      | cons right rest=>
        have pieces : shapeOfHOLExact left=.one ∧ shapeOfHOLExact right=.one ∧ rest.map shapeOfHOLExact=[] := by
          simpa only [List.map_cons,List.cons.injEq] using shapes
        have empty : rest=[] := by cases rest with | nil=>rfl | cons head tail=>cases pieces.2.2
        obtain ⟨a,rfl⟩ := RlpWrite.U256Value.scalar_word left pieces.1
        obtain ⟨b,rfl⟩ := RlpWrite.U256Value.scalar_word right pieces.2.1
        subst rest
        exact ⟨a,b,rfl⟩

end InitECandidate.Solver.Input.ScalarPair

#print axioms InitECandidate.Solver.Input.ScalarPair.of_shape
