import InitECandidate.Solver.Rlp.HeaderCall

namespace InitECandidate.Solver.Rlp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Shared original p/len calling convention, parametrized by the actual
function name and body. -/
theorem environment (table : MlS → Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function : MlS) (body : ProgHOL 64) (shape : ShapeHOL) (pointer length : BitVec 64)
    (known : table function=some (Header.formals,body,shape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table function (Header.values pointer length)=some (body,callee,shape) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "len")=some (.val (.word length)) := by
  have valid : (Header.formals.map Prod.fst).Nodup ∧ Header.formals.length=(Header.values pointer length).length ∧
      ((Header.formals.zip (Header.values pointer length)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [Header.formals,Header.values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact table function (Header.values pointer length)=some (body,Header.rawLocals pointer length,shape) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  · rw [locals]
    simp [Header.rawLocals,show ofString "p"≠ofString "len" from by decide]
  · rw [locals]
    simp [Header.rawLocals]

end InitECandidate.Solver.Rlp

#print axioms InitECandidate.Solver.Rlp.environment
