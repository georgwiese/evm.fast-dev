import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.CurrentStartup.BlsConstsInit

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace BlsLibInit
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .bls_lib_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_lib_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (key cursor) code _ _
  (GlobalEffects.call_body (key cursor) code (some none) (Code.name .bls_consts_init) _ (Code.formals .bls_consts_init) (Code.body .bls_consts_init) (Code.shape .bls_consts_init)
  (Code.installed code installed .bls_consts_init) (BlsConstsInit.preserves cursor code installed))
  (GlobalEffects.returned (key cursor) code _))

end BlsLibInit
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.BlsLibInit.preserves
