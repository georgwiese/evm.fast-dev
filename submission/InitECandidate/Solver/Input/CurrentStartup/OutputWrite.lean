import InitECandidate.Solver.Input.CurrentStartup.Base

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace OutputWrite
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .output_write) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_output_write, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (key cursor) code _ _ _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.loop (key cursor) code _ _
  (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.shared_store (key cursor) code _ _ _)
  (GlobalEffects.assign (key cursor) code _ _)))
  (GlobalEffects.returned (key cursor) code _)))

end OutputWrite
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.OutputWrite.preserves
