import InitECandidate.Solver.Input.MainRootAllocation

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_htr_new_payload_request with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "si",.one),(ofString "out",.one)]
def values (si root : BitVec 64) : List (ValueHOL 64) := [.val (.word si),.val (.word root)]
def rawLocals (si root : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word root)) else if name=ofString "si" then some (.val (.word si)) else none

/-- Installed literal original htr_new_payload_request203 and its real ABI. -/
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htr_new_payload_request")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 203 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htr_new_payload_request) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_htr_new_payload_request,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (si root : BitVec 64)
    (code : codeFn (ofString "htr_new_payload_request")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htr_new_payload_request") (values si root)=some (body,callee,.one) ∧
      callee.lookup (ofString "si")=some (.val (.word si)) ∧ callee.lookup (ofString "out")=some (.val (.word root)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values si root).length ∧
      ((formals.zip (values si root)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htr_new_payload_request") (values si root)=some (body,rawLocals si root,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  · rw [locals]; simp [rawLocals,show ofString "si"≠ofString "out" from by decide]
  · rw [locals]; simp [rawLocals]

theorem main_arguments (input : Guest.InputBlob) (caller source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (actual : Main.DecoderCall.DecoderReady input caller source) :
    evalListHOLFinite (Main.RequestHash.entered source root) (h:=fun address=>Classical.propDecidable ((Main.RequestHash.entered source root).memaddrs address)) Main.RequestHash.arguments=
      some (values (Main.RequestPrefix.cursor input) root) := by
  have fields := Main.RequestHash.entered_fields input caller source root actual
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,Main.RequestHash.arguments,QueryBranch.localVar,fields.1,fields.2.1,values]

end InitECandidate.Solver.Input.RequestRootHash

#print axioms InitECandidate.Solver.Input.RequestRootHash.original_code
#print axioms InitECandidate.Solver.Input.RequestRootHash.environment
#print axioms InitECandidate.Solver.Input.RequestRootHash.main_arguments
