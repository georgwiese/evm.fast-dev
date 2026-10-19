import InitECandidate.Solver.GasBudget.WarmAddressProgram
import InitECandidate.Solver.Input.NoExceptionLoop
import InitECandidate.Solver.Input.NoExceptionScoped

namespace InitECandidate.Solver.MutableTable.QueryNoException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- Original hash probes never raise a source exception, at any clock.
Malformed reads/errors and timeout are retained; this asserts no termination. -/
theorem hash_safe (code) : Input.NoException.Safe code Hash.body := by
  simp only [Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoException.sequence
    | apply Input.NoException.declared
    | apply Input.NoException.conditional
    | apply Input.NoException.loop
    | exact Input.NoException.assign code _ _
    | exact Input.NoException.returned code _
    | exact Input.NoException.skip code

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem memeq_safe (code) : Input.NoException.Safe code WitnessRadix.Memeq32.body := by
  simp only [WitnessRadix.Memeq32.body, Guest.guestFn_memeq, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoException.sequence
    | apply Input.NoException.declared
    | apply Input.NoException.conditional
    | apply Input.NoException.loop
    | exact Input.NoException.assign code _ _
    | exact Input.NoException.returned code _
    | exact Input.NoException.skip code

theorem find_safe (code)
    (hashCode : code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (memeqCode : code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one)) :
    Input.NoException.Safe code Find.body := by
  simp only [Find.body, Guest.guestFn_htab_find_slot, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoException.sequence
    | apply Input.NoException.declared
    | apply Input.NoException.conditional
    | apply Input.NoException.loop
    | exact Input.NoException.assign code _ _
    | exact Input.NoException.returned code _
    | exact Input.NoException.skip code
    | apply Input.NoException.scoped_body code "h" .one (ofString "htab_hash") _ _ Hash.formals Hash.body .one hashCode (hash_safe code)
    | apply Input.NoException.scoped_body code "eq" .one (ofString "memeq") _ _ WitnessRadix.Memeq32.formals WitnessRadix.Memeq32.body .one memeqCode (memeq_safe code)

theorem has_safe (code)
    (hashCode : code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (memeqCode : code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (findCode : code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one)) :
    Input.NoException.Safe code Has.body := by
  rw [Has.body_shape]
  apply Input.NoException.scoped_body code "i" .one (ofString "htab_find_slot") _ _ Find.formals Find.body .one findCode (find_safe code hashCode memeqCode)
  unfold Has.afterIndex Has.absent Has.present
  exact Input.NoException.sequence code _ _
    (Input.NoException.conditional code _ _ _ (Input.NoException.returned code _) (Input.NoException.skip code))
    (Input.NoException.returned code _)

end InitECandidate.Solver.MutableTable.QueryNoException

namespace InitECandidate.Solver.GasBudget.WarmAddress
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString MutableTable

theorem safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : WarmKeys.Environment source)
    (installed : Input.OriginalCode.Installed source.code) : Input.NoException.Safe source.code body := by
  rw [body_shape]
  exact Input.NoException.scoped_body source.code "h" .one (ofString "htab_has") _ _ Has.formals Has.body .one
    (has_code source.code installed) (QueryNoException.has_safe source.code environment.hashCode environment.memeqCode environment.findCode)
    (Input.NoException.returned source.code _)

end InitECandidate.Solver.GasBudget.WarmAddress

#print axioms InitECandidate.Solver.MutableTable.QueryNoException.hash_safe
#print axioms InitECandidate.Solver.MutableTable.QueryNoException.memeq_safe
#print axioms InitECandidate.Solver.MutableTable.QueryNoException.find_safe
#print axioms InitECandidate.Solver.MutableTable.QueryNoException.has_safe
#print axioms InitECandidate.Solver.GasBudget.WarmAddress.safe
