import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Checked lookup identifies a known first word binding even when the
second argument value is unrestricted. No successful helper run is assumed. -/
theorem checked_pair_left (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function firstName secondName : MlS) (body : ProgHOL 64) (resultShape : ShapeHOL) (pointer : BitVec 64) (value : ValueHOL 64)
    (different : firstName≠secondName)
    (known : table function=some ([(firstName,.one),(secondName,.one)],body,resultShape))
    (actualBody : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite table function [.val (.word pointer),value]=some (actualBody,callee,shape)) :
    actualBody=body ∧ callee.lookup firstName=some (.val (.word pointer)) := by
  have raw := lookupCodeHOLFinite_eq_some table function _ actualBody callee shape called
  simp only [lookupCodeHOLExact,known] at raw
  split at raw
  · have bodyEq : body=actualBody := congrArg Prod.fst (Option.some.inj raw)
    have localsEq := congrArg (fun triple => triple.2.1) (Option.some.inj raw)
    dsimp only at localsEq
    refine ⟨bodyEq.symm,?_⟩
    rw [←localsEq]
    simp [FUPDATE,different,Ne.symm different]
  · cases raw

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.checked_pair_left
