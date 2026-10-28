import InitECandidate.Solver.Mpt.StateInitProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (nodes root codes : BitVec 64) : List (ValueHOL 64) := [.val (.word nodes),.val (.word root),.val (.word codes)]
def rawLocals (nodes root codes : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "codedb" then some (.val (.word codes)) else if name=ofString "state_root" then some (.val (.word root)) else
    if name=ofString "nodedb" then some (.val (.word nodes)) else none

/-- The original three-formal lookup installs exactly the actual node,
root and code words, with no assumed successful state initialization. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (nodes root codes : BitVec 64)
    (code : codeFn (ofString "state_init")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "state_init") (values nodes root codes)=some (body,callee,.one) ∧
      callee.lookup (ofString "nodedb")=some (.val (.word nodes)) ∧ callee.lookup (ofString "state_root")=some (.val (.word root)) ∧
      callee.lookup (ofString "codedb")=some (.val (.word codes)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values nodes root codes).length ∧
      ((formals.zip (values nodes root codes)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "state_init") (values nodes root codes)=some (body,rawLocals nodes root codes,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,show ofString "nodedb"≠ofString "codedb" from by decide,
    show ofString "nodedb"≠ofString "state_root" from by decide,show ofString "state_root"≠ofString "codedb" from by decide]

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.environment
