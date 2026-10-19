import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.ReturnGuardNormal
import InitECandidate.Solver.Input.NoException

namespace InitECandidate.Solver.GasBudget.ValidDelegation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_is_valid_delegation with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "code", .one), (ofString "n", .one)]
def lengthTest : ExpHOL 64 := match body with | .seq (.ite test _ _) _ => test | _ => .const 0#64
def afterLength : ProgHOL 64 := match body with | .seq _ rest => rest | _ => .skip
def bytesTest : ExpHOL 64 := match afterLength with | .seq (.ite test _ _) _ => test | _ => .const 0#64

theorem body_shape : body = .seq (.ite lengthTest (.return (.const 0#64)) .skip) afterLength := by
  simp only [body, Guest.guestFn_is_valid_delegation, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    lengthTest, afterLength]
theorem tail_shape : afterLength = .seq (.ite bytesTest (.return (.const 1#64)) .skip) (.return (.const 0#64)) := by
  simp only [body, Guest.guestFn_is_valid_delegation, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    afterLength, bytesTest]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "is_valid_delegation") = some (formals, body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 404 (OriginalCodeEnvironment.originalEntry Guest.guestFn_is_valid_delegation) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals,
    Guest.guestFn_is_valid_delegation, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

/-- Every actual normal recognizer run is a binary return, empties locals
and leaves every other state field, including the source clock, unchanged. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    (returned = .val (.word 0#64) ∨ returned = .val (.word 1#64)) ∧ post = emptyLocalsHOLFinite source := by
  rw [body_shape] at run
  rcases Input.return_guard_normal source post lengthTest (.const 0#64) afterLength returned run with stopped | continued
  · obtain ⟨read, stateEq⟩ := stopped
    exact ⟨Or.inl (Option.some.inj (read.symm.trans rfl)), stateEq⟩
  · rw [tail_shape] at continued
    rcases Input.return_guard_normal source post bytesTest (.const 1#64) (.return (.const 0#64)) returned continued with stopped | continued
    · obtain ⟨read, stateEq⟩ := stopped
      exact ⟨Or.inr (Option.some.inj (read.symm.trans rfl)), stateEq⟩
    · obtain ⟨read, stateEq⟩ := Input.return_normal source post (.const 0#64) returned continued
      exact ⟨Or.inl (Option.some.inj (read.symm.trans rfl)), stateEq⟩

theorem safe (code) : Input.NoException.Safe code body := by
  rw [body_shape, tail_shape]
  repeat first
    | apply Input.NoException.sequence
    | apply Input.NoException.conditional
    | exact Input.NoException.returned code _
    | exact Input.NoException.skip code

end InitECandidate.Solver.GasBudget.ValidDelegation

#print axioms InitECandidate.Solver.GasBudget.ValidDelegation.body_shape
#print axioms InitECandidate.Solver.GasBudget.ValidDelegation.tail_shape
#print axioms InitECandidate.Solver.GasBudget.ValidDelegation.original_code
#print axioms InitECandidate.Solver.GasBudget.ValidDelegation.body_normal
#print axioms InitECandidate.Solver.GasBudget.ValidDelegation.safe
