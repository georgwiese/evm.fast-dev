import InitECandidate.Solver.Input.PayloadHeaderProgram
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS×ShapeHOL):=[(ofString "si",.one)]
def values (si : BitVec 64) : List (ValueHOL 64):=[.val (.word si)]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "payload_header")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 800 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_payload_header) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_payload_header,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (si : BitVec 64)
    (code : codeFn (ofString "payload_header")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "payload_header") (values si)=some (body,callee,.one) ∧
      callee.lookup (ofString "si")=some (.val (.word si)) :=
  word_environment codeFn (ofString "payload_header") (ofString "si") body .one si code

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.original_code
#print axioms InitECandidate.Solver.Input.PayloadHeader.environment
