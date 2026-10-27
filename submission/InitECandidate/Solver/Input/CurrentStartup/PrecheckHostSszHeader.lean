import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.HostInputByte
import InitECandidate.Solver.Input.CurrentStartup.HostInputLe32
import InitECandidate.Solver.Input.CurrentStartup.SszCheckOffsets
import InitECandidate.Solver.Input.CurrentStartup.SszFail

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace PrecheckHostSszHeader
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .precheck_host_ssz_header) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_precheck_host_ssz_header, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.shared_load (key cursor) code _ _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.returned (key cursor) code _)
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (HostInputByte.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (HostInputByte.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (HostInputLe32.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (HostInputLe32.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (SszCheckOffsets.preserves cursor code installed))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (HostInputLe32.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (HostInputLe32.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (HostInputLe32.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (SszCheckOffsets.preserves cursor code installed))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.conditional (key cursor) code _ _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (SszFail.preserves cursor code installed))
  (GlobalEffects.skip (key cursor) code))
  (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (HostInputLe32.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (HostInputLe32.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (HostInputLe32.preserves cursor code installed)
  (GlobalEffects.scoped_body (key cursor) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (HostInputLe32.preserves cursor code installed)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.store (key cursor) code _ _)
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (SszCheckOffsets.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _)))))))))))))))))))))))))))))))))))))

end PrecheckHostSszHeader
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.PrecheckHostSszHeader.preserves
