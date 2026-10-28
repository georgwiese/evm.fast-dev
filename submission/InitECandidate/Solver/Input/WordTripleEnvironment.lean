import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Three actual scalar formal parameters determine the concrete finite
callee environment; parameter names may be any distinct original names. -/
theorem word_triple_environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function firstName secondName thirdName : MlS) (body : ProgHOL 64) (shape : ShapeHOL) (first second third : BitVec 64)
    (firstSecond : firstName≠secondName) (firstThird : firstName≠thirdName) (secondThird : secondName≠thirdName)
    (known : table function=some ([(firstName,.one),(secondName,.one),(thirdName,.one)],body,shape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table function [.val (.word first),.val (.word second),.val (.word third)]=some (body,callee,shape) ∧
      callee.lookup firstName=some (.val (.word first)) ∧ callee.lookup secondName=some (.val (.word second)) ∧
      callee.lookup thirdName=some (.val (.word third)) := by
  let formals : List (MlS×ShapeHOL) := [(firstName,.one),(secondName,.one),(thirdName,.one)]
  let values : List (ValueHOL 64) := [.val (.word first),.val (.word second),.val (.word third)]
  let rawLocals : MlS→Option (ValueHOL 64) := fun key=>if key=thirdName then some (.val (.word third)) else if key=secondName then some (.val (.word second)) else if key=firstName then some (.val (.word first)) else none
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=values.length ∧
      ((formals.zip values).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    exact ⟨by simp [formals,firstSecond,firstThird,secondThird],rfl,by simp [formals,values,shapeEqHOL,shapeOfHOLExact]⟩
  have raw : lookupCodeHOLExact table function values=some (body,rawLocals,shape) := by
    change table function=some (formals,body,shape) at known
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,firstThird,firstSecond],
    by rw [locals]; simp [rawLocals,secondThird],by rw [locals]; simp [rawLocals]⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.word_triple_environment

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def tripleValues (p n out : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word p), .val (.word n), .val (.word out)]

/-- The common p/n/out ABI specializes the arbitrary-name three-word interface. -/
theorem triple_environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function : MlS) (body : ProgHOL 64) (p n out : BitVec 64)
    (code : codeFn function = some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)], body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), lookupCodeHOLFinite codeFn function (tripleValues p n out) = some (body, callee, .one) ∧
      callee.lookup (ofString "p") = some (.val (.word p)) ∧ callee.lookup (ofString "n") = some (.val (.word n)) ∧ callee.lookup (ofString "out") = some (.val (.word out)) :=
  word_triple_environment codeFn function (ofString "p") (ofString "n") (ofString "out") body .one p n out
    (by decide) (by decide) (by decide) code

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.triple_environment
