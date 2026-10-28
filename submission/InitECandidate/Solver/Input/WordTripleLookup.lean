import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actual checked three-word ABI lookup identifies its last pointer
binding while the first two argument values remain unrestricted. -/
theorem checked_triple_last (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function firstName secondName lastName : MlS) (body : ProgHOL 64) (resultShape : ShapeHOL)
    (left right : ValueHOL 64) (pointer : BitVec 64)
    (known : table function=some ([(firstName,.one),(secondName,.one),(lastName,.one)],body,resultShape))
    (actualBody : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite table function [left,right,.val (.word pointer)]=some (actualBody,callee,shape)) :
    actualBody=body ∧ callee.lookup lastName=some (.val (.word pointer)) := by
  have raw := lookupCodeHOLFinite_eq_some table function _ actualBody callee shape called
  simp only [lookupCodeHOLExact,known] at raw
  split at raw
  · have bodyEq : body=actualBody := congrArg Prod.fst (Option.some.inj raw)
    have localsEq := congrArg (fun triple=>triple.2.1) (Option.some.inj raw)
    dsimp only at localsEq
    refine ⟨bodyEq.symm,?_⟩
    rw [←localsEq]
    simp
  · cases raw

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.checked_triple_last
