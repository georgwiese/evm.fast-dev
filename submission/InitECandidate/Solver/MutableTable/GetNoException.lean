import InitECandidate.Solver.MutableTable.QueryNoException
import InitECandidate.Solver.MutableTable.GetNormalCall

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "htab_get") = some (formals, body, pairShape) := by
  have checked := Input.OriginalCode.indexed code installed 120 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_get) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals, Find.formals, pairShape,
    Guest.guestFn_htab_get, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem safe (code)
    (hashCode : code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (memeqCode : code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (findCode : code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one)) :
    Input.NoException.Safe code body := by
  simp only [body, Guest.guestFn_htab_get, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoException.sequence
    | apply Input.NoException.declared
    | apply Input.NoException.conditional
    | exact Input.NoException.returned code _
    | exact Input.NoException.skip code
    | apply Input.NoException.scoped_body code "i" .one (ofString "htab_find_slot") _ _ Find.formals Find.body .one
        findCode (QueryNoException.find_safe code hashCode memeqCode)

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.original_code
#print axioms InitECandidate.Solver.MutableTable.Get.safe
