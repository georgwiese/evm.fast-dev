import InitECandidate.Solver.MutableTable.WitnessBuildAnyClock
import InitECandidate.Solver.MutableTable.WitnessBuildEmptyAnyClock
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def formals : List (MlS×ShapeHOL) := [(ofString "slice_arr",.one),(ofString "n",.one)]
def values (array : BitVec 64) (count : Nat) : List (ValueHOL 64) := [.val (.word array),.val (.word (BitVec.ofNat 64 count))]
def rawLocals (array : BitVec 64) (count : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 count))) else if name=ofString "slice_arr" then some (.val (.word array)) else none

set_option maxRecDepth 100000 in
/-- Literal original nodedb_build229, with no replacement constructor. -/
theorem original_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "nodedb_build")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 229 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_nodedb_build) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_nodedb_build,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (array : BitVec 64) (count : Nat)
    (code : codeFn (ofString "nodedb_build")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "nodedb_build") (values array count)=some (body,callee,.one) ∧
      callee.lookup (ofString "slice_arr")=some (.val (.word array)) ∧ callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values array count).length ∧
      ((formals.zip (values array count)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "nodedb_build") (values array count)=some (body,rawLocals array count,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "slice_arr"≠ofString "n" from by decide],by rw [locals]; simp [rawLocals]⟩

end InitECandidate.Solver.MutableTable.WitnessBuild
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.original_code
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.environment
