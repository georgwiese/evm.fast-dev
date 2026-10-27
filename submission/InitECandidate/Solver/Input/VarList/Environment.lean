import InitECandidate.Solver.Input.VarList.Program
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def returnShape : ShapeHOL := .comb [.one,.one]
def values (pointer length limit : BitVec 64) : List (ValueHOL 64) := [.val (.word pointer),.val (.word length),.val (.word limit)]
def rawLocals (pointer length limit : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "lim" then some (.val (.word limit)) else if name=ofString "len" then some (.val (.word length))
  else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer length limit : BitVec 64)
    (code : codeFn (ofString "ssz_split_var_list")=some (formals,body,returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "ssz_split_var_list") (values pointer length limit)=some (body,callee,returnShape) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "len")=some (.val (.word length)) ∧
      callee.lookup (ofString "lim")=some (.val (.word limit)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer length limit).length ∧
      ((formals.zip (values pointer length limit)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "ssz_split_var_list") (values pointer length limit)=some (body,rawLocals pointer length limit,returnShape) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "p"≠ofString "lim" from by decide,show ofString "p"≠ofString "len" from by decide]
  · simp [rawLocals,show ofString "len"≠ofString "lim" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.environment
