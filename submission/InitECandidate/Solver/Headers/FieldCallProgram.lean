import InitECandidate.Solver.Headers.FieldProgram

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def Kind.values (kind : Kind) (array index control : BitVec 64) : List (ValueHOL 64) :=
  match kind with
  | .raw=>[.val (.word array),.val (.word index)]
  | _=>[.val (.word array),.val (.word index),.val (.word control)]
def Kind.controlName : Kind→MlS | .uint=>ofString "maxb" | .bytes=>ofString "width" | .raw=>ofString ""
def Kind.rawLocals (kind : Kind) (array index control : BitVec 64) (key : MlS) : Option (ValueHOL 64) :=
  match kind with
  | .uint=>if key=ofString "maxb" then some (.val (.word control)) else if key=ofString "i" then some (.val (.word index)) else if key=ofString "arr" then some (.val (.word array)) else none
  | .bytes=>if key=ofString "width" then some (.val (.word control)) else if key=ofString "i" then some (.val (.word index)) else if key=ofString "arr" then some (.val (.word array)) else none
  | .raw=>if key=ofString "i" then some (.val (.word index)) else if key=ofString "arr" then some (.val (.word array)) else none

/-- Original two/three-word caller ABI, including actual selected index and
width/max-byte control; no future helper outputs are supplied. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (kind : Kind) (array index control : BitVec 64)
    (code : codeFn kind.name=some (kind.formals,kind.body,kind.resultShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn kind.name (kind.values array index control)=some (kind.body,callee,kind.resultShape) ∧
      callee.lookup (ofString "arr")=some (.val (.word array)) ∧ callee.lookup (ofString "i")=some (.val (.word index)) ∧
      (kind≠.raw → callee.lookup kind.controlName=some (.val (.word control))) := by
  have valid : (kind.formals.map Prod.fst).Nodup ∧ kind.formals.length=(kind.values array index control).length ∧
      ((kind.formals.zip (kind.values array index control)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    cases kind <;> exact ⟨by decide,rfl,by simp [Kind.formals,Kind.values,shapeEqHOL,shapeOfHOLExact]⟩
  have raw : lookupCodeHOLExact codeFn kind.name (kind.values array index control)=some (kind.body,kind.rawLocals array index control,kind.resultShape) := by
    simp only [lookupCodeHOLExact,code,valid]
    cases kind <;> rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  · rw [locals]
    cases kind <;> simp [Kind.rawLocals,
      show ofString "arr"≠ofString "maxb" from by decide,
      show ofString "arr"≠ofString "width" from by decide,
      show ofString "arr"≠ofString "i" from by decide,
      show ofString "i"≠ofString "maxb" from by decide,
      show ofString "i"≠ofString "width" from by decide]
  · rw [locals]
    cases kind <;> simp [Kind.rawLocals,
      show ofString "arr"≠ofString "maxb" from by decide,
      show ofString "arr"≠ofString "width" from by decide,
      show ofString "arr"≠ofString "i" from by decide,
      show ofString "i"≠ofString "maxb" from by decide,
      show ofString "i"≠ofString "width" from by decide]
  · intro nonraw
    rw [locals]
    cases kind <;> simp_all [Kind.rawLocals,Kind.controlName]

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.environment
