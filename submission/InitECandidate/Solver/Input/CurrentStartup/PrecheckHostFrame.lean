import InitECandidate.Solver.Input.CurrentStartup.Code
import InitECandidate.Solver.Input.ReadHostScoped

namespace InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

-- Generated actual-syntax proof terms; Lean must validate the source oracle
-- and every all-outcome call/loop composition. Events need not be unchanged.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ssz_fail (code) (installed : OriginalCode.Installed code) :
    ReadHostEffects.Preserves code (Code.body .ssz_fail) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_fail, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (ReadHostEffects.sequence code _ _
  (ReadHostEffects.raised code _ _)
  (ReadHostEffects.returned code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem host_input_byte (code) (installed : OriginalCode.Installed code) :
    ReadHostEffects.Preserves code (Code.body .host_input_byte) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_host_input_byte, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (ReadHostEffects.declared code _ _ _ _
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.shared_load code _ _ _)
  (ReadHostEffects.returned code _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem host_input_le32 (code) (installed : OriginalCode.Installed code) :
    ReadHostEffects.Preserves code (Code.body .host_input_le32) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_host_input_le32, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed)
  (ReadHostEffects.returned code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ssz_check_offsets (code) (installed : OriginalCode.Installed code) :
    ReadHostEffects.Preserves code (Code.body .ssz_check_offsets) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_check_offsets, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.returned code _)
  (ReadHostEffects.skip code))
  (ReadHostEffects.declared code _ _ _ _
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.loop code _ _
  (ReadHostEffects.declared code _ _ _ _
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed))
  (ReadHostEffects.skip code))
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed))
  (ReadHostEffects.skip code))
  (ReadHostEffects.skip code))
  (ReadHostEffects.assign code _ _)))))
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed))
  (ReadHostEffects.skip code))
  (ReadHostEffects.returned code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem precheck_host_ssz_header (code) (installed : OriginalCode.Installed code) :
    ReadHostEffects.Preserves code (Code.body .precheck_host_ssz_header) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_precheck_host_ssz_header, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (ReadHostEffects.declared code _ _ _ _
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.shared_load code _ _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.returned code _)
  (ReadHostEffects.skip code))
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed))
  (ReadHostEffects.skip code))
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed))
  (ReadHostEffects.skip code))
  (ReadHostEffects.declared code _ _ _ _
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed))
  (ReadHostEffects.skip code))
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.store code _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.store code _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed))
  (ReadHostEffects.declared code _ _ _ _
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed))
  (ReadHostEffects.skip code))
  (ReadHostEffects.declared code _ _ _ _
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.store code _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.store code _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.store code _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed))
  (ReadHostEffects.declared code _ _ _ _
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.conditional code _ _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed))
  (ReadHostEffects.skip code))
  (ReadHostEffects.declared code _ _ _ _
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed)
  (ReadHostEffects.scoped_body code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.store code _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.store code _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.store code _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.store code _ _)
  (ReadHostEffects.sequence code _ _
  (ReadHostEffects.call_body code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed))
  (ReadHostEffects.returned code _)))))))))))))))))))))))))))))))))))))

end InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck

#print axioms InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck.ssz_fail
#print axioms InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck.host_input_byte
#print axioms InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck.host_input_le32
#print axioms InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck.ssz_check_offsets
#print axioms InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck.precheck_host_ssz_header
