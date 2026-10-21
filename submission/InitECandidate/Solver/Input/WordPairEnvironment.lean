import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actual original two-word signature determines both current callee
bindings, for arbitrary distinct parameter names and returned shape. -/
theorem word_pair_environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function leftName rightName : MlS) (body : ProgHOL 64) (shape : ShapeHOL) (left right : BitVec 64)
    (distinct : leftName≠rightName)
    (known : table function=some ([(leftName,.one),(rightName,.one)],body,shape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table function [.val (.word left),.val (.word right)]=some (body,callee,shape) ∧
      callee.lookup leftName=some (.val (.word left)) ∧ callee.lookup rightName=some (.val (.word right)) := by
  let formals : List (MlS×ShapeHOL) := [(leftName,.one),(rightName,.one)]
  let values : List (ValueHOL 64) := [.val (.word left),.val (.word right)]
  let rawLocals : MlS→Option (ValueHOL 64) := fun key=>if key=rightName then some (.val (.word right)) else if key=leftName then some (.val (.word left)) else none
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=values.length ∧
      ((formals.zip values).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    exact ⟨by simp [formals,distinct],rfl,by simp [formals,values,shapeEqHOL,shapeOfHOLExact]⟩
  have raw : lookupCodeHOLExact table function values=some (body,rawLocals,shape) := by
    change table function=some (formals,body,shape) at known
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,distinct],by rw [locals]; simp [rawLocals]⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.word_pair_environment
