import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.DecodeStatelessInput
import InitECandidate.Solver.Input.CurrentStartup.InputBlob
import InitECandidate.Solver.Input.CurrentStartup.PrecheckHostSszHeader

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace DecodeHostInput
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .decode_host_input) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_decode_host_input, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .precheck_host_ssz_header) _ (Code.formals .precheck_host_ssz_header) (Code.body .precheck_host_ssz_header) (Code.shape .precheck_host_ssz_header)
  (Code.installed code installed .precheck_host_ssz_header) (PrecheckHostSszHeader.preserves cursor code installed))
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .input_blob) _ _ (Code.formals .input_blob) (Code.body .input_blob) (Code.shape .input_blob)
  (Code.installed code installed .input_blob) (InputBlob.preserves cursor code installed)
  (GlobalEffects.call_body (key cursor) code none (Code.name .decode_stateless_input) _ (Code.formals .decode_stateless_input) (Code.body .decode_stateless_input) (Code.shape .decode_stateless_input)
  (Code.installed code installed .decode_stateless_input) (DecodeStatelessInput.preserves cursor code installed))))

end DecodeHostInput
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecodeHostInput.preserves
