import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- One original scalar formal supplies its actual finite callee binding. -/
theorem word_environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function formal : MlS) (body : ProgHOL 64) (shape : ShapeHOL) (word : BitVec 64)
    (known : table function=some ([(formal,.one)],body,shape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite table function [.val (.word word)]=some (body,callee,shape) ∧
      callee.lookup formal=some (.val (.word word)) := by
  let formals : List (MlS×ShapeHOL) := [(formal,.one)]
  let values : List (ValueHOL 64) := [.val (.word word)]
  let rawLocals : MlS→Option (ValueHOL 64) := fun key=>if key=formal then some (.val (.word word)) else none
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=values.length ∧
      ((formals.zip values).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    exact ⟨by simp [formals],rfl,by simp [formals,values,shapeEqHOL,shapeOfHOLExact]⟩
  have raw : lookupCodeHOLExact table function values=some (body,rawLocals,shape) := by
    change table function=some (formals,body,shape) at known
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals]⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.word_environment
