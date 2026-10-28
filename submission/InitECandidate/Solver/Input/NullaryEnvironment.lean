import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An installed zero-argument signature supplies the genuine finite callee
lookup without any premise about its eventual execution. -/
theorem nullary_environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (name : MlS) (body : ProgHOL 64) (shape : ShapeHOL)
    (known : codeFn name=some ([],body,shape)) :
    ∃ callee,lookupCodeHOLFinite codeFn name []=some (body,callee,shape) := by
  have raw : lookupCodeHOLExact codeFn name []=some (body,(fun _=>none),shape) := by
    simp [lookupCodeHOLExact,known]
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn name [] body _ shape raw
  exact ⟨callee,called⟩

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.nullary_environment
