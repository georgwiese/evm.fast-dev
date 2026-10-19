import InitECandidate.Solver.Mpt.TrieWalkProgram
import InitECandidate.Solver.Input.LocalEffectsScoped
import InitECandidate.Solver.Input.NoNamedExceptionLoop

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem memeq_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 13 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_memeq) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, WitnessRadix.Memeq32.body, WitnessRadix.Memeq32.formals,
    Guest.guestFn_memeq, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem memeq_readonly (code) : Input.LocalEffects.Preserves code WitnessRadix.Memeq32.body := by
  simp only [WitnessRadix.Memeq32.body, Guest.guestFn_memeq, progToHOL]
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.conditional
    | apply Input.LocalEffects.loop
    | exact Input.LocalEffects.assign code _ _
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Every original walk outcome preserves memory, globals, FFI and metadata.
The source clock is erased here; termination and loop prices are separate. -/
theorem readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code body := by
  simp only [body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.conditional
    | apply Input.LocalEffects.loop
    | exact Input.LocalEffects.assign code _ _
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code
    | exact Input.LocalEffects.call_body code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Fail.readonly code)
    | apply Input.LocalEffects.scoped_body code (ofString "eq") .one (ofString "memeq") _ _ WitnessRadix.Memeq32.formals WitnessRadix.Memeq32.body .one
        (memeq_code code installed) (memeq_readonly code)
    | apply Input.LocalEffects.scoped_body code (ofString "eq2") .one (ofString "memeq") _ _ WitnessRadix.Memeq32.formals WitnessRadix.Memeq32.body .one
        (memeq_code code installed) (memeq_readonly code)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem no_other_exception (code) (installed : Input.OriginalCode.Installed code)
    (forbidden : MlS) (other : ofString "MptErr" ≠ forbidden) : Input.NoNamedException.Safe code forbidden body := by
  simp only [body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoNamedException.sequence
    | apply Input.NoNamedException.declared
    | apply Input.NoNamedException.conditional
    | apply Input.NoNamedException.loop
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.assign code _ _)
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.returned code _)
    | exact Input.NoNamedException.of_all code _ _ (Input.NoException.skip code)
    | exact Input.NoNamedException.call_body code forbidden (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Fail.no_other_exception code forbidden other)
    | apply Input.NoNamedException.scoped_body code forbidden "eq" .one (ofString "memeq") _ _ WitnessRadix.Memeq32.formals WitnessRadix.Memeq32.body .one
        (memeq_code code installed) (Input.NoNamedException.of_all code _ _ (MutableTable.QueryNoException.memeq_safe code))
    | apply Input.NoNamedException.scoped_body code forbidden "eq2" .one (ofString "memeq") _ _ WitnessRadix.Memeq32.formals WitnessRadix.Memeq32.body .one
        (memeq_code code installed) (Input.NoNamedException.of_all code _ _ (MutableTable.QueryNoException.memeq_safe code))

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.memeq_code
#print axioms InitECandidate.Solver.Mpt.TrieWalk.memeq_readonly
#print axioms InitECandidate.Solver.Mpt.TrieWalk.readonly
#print axioms InitECandidate.Solver.Mpt.TrieWalk.no_other_exception
