import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Four distinct actual scalar formals determine their genuine finite
callee bindings, without a premise about successful function execution. -/
theorem word_quad_environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function firstName secondName thirdName fourthName : MlS) (body : ProgHOL 64) (shape : ShapeHOL)
    (first second third fourth : BitVec 64)
    (firstSecond : firstName≠secondName) (firstThird : firstName≠thirdName) (firstFourth : firstName≠fourthName)
    (secondThird : secondName≠thirdName) (secondFourth : secondName≠fourthName) (thirdFourth : thirdName≠fourthName)
    (known : table function=some ([(firstName,.one),(secondName,.one),(thirdName,.one),(fourthName,.one)],body,shape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table function [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]=some (body,callee,shape) ∧
      callee.lookup firstName=some (.val (.word first)) ∧ callee.lookup secondName=some (.val (.word second)) ∧
      callee.lookup thirdName=some (.val (.word third)) ∧ callee.lookup fourthName=some (.val (.word fourth)) := by
  let formals : List (MlS×ShapeHOL):=[(firstName,.one),(secondName,.one),(thirdName,.one),(fourthName,.one)]
  let values : List (ValueHOL 64):=[.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]
  let rawLocals : MlS→Option (ValueHOL 64):=fun key=>
    if key=fourthName then some (.val (.word fourth)) else if key=thirdName then some (.val (.word third))
    else if key=secondName then some (.val (.word second)) else if key=firstName then some (.val (.word first)) else none
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=values.length ∧
      ((formals.zip values).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=by
    exact ⟨by simp [formals,firstSecond,firstThird,firstFourth,secondThird,secondFourth,thirdFourth],rfl,
      by simp [formals,values,shapeEqHOL,shapeOfHOLExact]⟩
  have raw : lookupCodeHOLExact table function values=some (body,rawLocals,shape):=by
    change table function=some (formals,body,shape) at known
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,firstFourth,firstThird,firstSecond],
    by rw [locals]; simp [rawLocals,secondFourth,secondThird],by rw [locals]; simp [rawLocals,thirdFourth],by rw [locals]; simp [rawLocals]⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.word_quad_environment
