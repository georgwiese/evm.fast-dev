import InitECandidate.Solver.Input.QuietReadOnlyCall
import InitECandidate.Solver.GasBudget.FrameField
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.GasBudget.RequireNotStatic
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64 := match Guest.guestFn_require_not_static with | .function fn => progToHOL fn.body | _ => .skip
def test : ExpHOL 64 := .cmp .notEqual (.load .one (.op .add [frameLoad 112#64, .const 144#64])) (.const 0#64)
def guard : ProgHOL 64 := .ite test (.raise (ofString "EvmErr") (.const 8#64)) .skip

theorem body_shape : body = .seq guard (.return (.const 0#64)) := by
  simp only [body, Guest.guestFn_require_not_static, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    guard, test, frameLoad, frameAddress]

theorem pure (code) : Input.LocalEffects.Preserves code body := by
  rw [body_shape]
  exact Input.LocalEffects.sequence code _ _
    (Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.raised code _ _) (Input.LocalEffects.skip code))
    (Input.LocalEffects.returned code _)

theorem quiet (code) : Input.QuietClock.Preserves code body := by
  rw [body_shape]
  exact Input.QuietClock.sequence code _ _
    (Input.QuietClock.conditional code _ _ _ (Input.QuietClock.raised code _ _) (Input.QuietClock.skip code))
    (Input.QuietClock.returned code _)

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "require_not_static") = some ([], body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[428]? =
      some (OriginalCodeEnvironment.originalEntry Guest.guestFn_require_not_static) := by rfl
  have checked := Input.OriginalCode.indexed code installed 428 _ found
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_require_not_static,
    body, shapeToHOL, List.map_nil] using checked

theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "require_not_static") []) = (none, post)) :
    1 ≤ source.clock ∧ post = {source with clock := source.clock - 1} :=
  Input.QuietReadOnlyCall.normal source post (ofString "require_not_static") [] [] body .one
    (original_code source.code installed) (pure source.code) (quiet source.code) normal

theorem call_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "require_not_static") []) = (some (.exception identifier payload), post)) :
    1 ≤ source.clock ∧ post.clock = source.clock - 1 ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 1} :=
  Input.QuietReadOnlyCall.exception source post (ofString "require_not_static") [] [] body .one
    (original_code source.code installed) (pure source.code) (quiet source.code) identifier payload run

end InitECandidate.Solver.GasBudget.RequireNotStatic

#print axioms InitECandidate.Solver.GasBudget.RequireNotStatic.body_shape
#print axioms InitECandidate.Solver.GasBudget.RequireNotStatic.pure
#print axioms InitECandidate.Solver.GasBudget.RequireNotStatic.quiet
#print axioms InitECandidate.Solver.GasBudget.RequireNotStatic.original_code
#print axioms InitECandidate.Solver.GasBudget.RequireNotStatic.call_normal
#print axioms InitECandidate.Solver.GasBudget.RequireNotStatic.call_exception
