import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.HostInputByte

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace HostInputLe32
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem any_key (selected : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves selected code (Code.body .host_input_le32) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_host_input_le32, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.scoped_body selected code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (HostInputByte.any_key selected code installed)
  (GlobalEffects.scoped_body selected code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (HostInputByte.any_key selected code installed)
  (GlobalEffects.scoped_body selected code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (HostInputByte.any_key selected code installed)
  (GlobalEffects.scoped_body selected code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (HostInputByte.any_key selected code installed)
  (GlobalEffects.returned selected code _)))))

theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .host_input_le32) :=
  any_key (key cursor) code installed

end HostInputLe32
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.HostInputLe32.preserves

#print axioms InitECandidate.Solver.Input.CurrentStartup.HostInputLe32.any_key
