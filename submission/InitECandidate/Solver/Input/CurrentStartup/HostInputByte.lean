import InitECandidate.Solver.Input.CurrentStartup.Base

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace HostInputByte
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem any_key (selected : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves selected code (Code.body .host_input_byte) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_host_input_byte, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared selected code _ _ _ _
  (GlobalEffects.sequence selected code _ _
  (GlobalEffects.shared_load selected code _ _ _)
  (GlobalEffects.returned selected code _)))

theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .host_input_byte) :=
  any_key (key cursor) code installed

end HostInputByte
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.HostInputByte.preserves

#print axioms InitECandidate.Solver.Input.CurrentStartup.HostInputByte.any_key
