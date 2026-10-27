import Guest.SoftwareAst
import InitECandidate.Solver.Input.NoReturn
import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Input.Trap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64 := match Guest.Software.guestFn_trap_with with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "code", .one)]
def values (word : BitVec 64) : List (ValueHOL 64) := [.val (.word word)]
def rawLocals (word : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "code" then some (.val (.word word)) else none

/-- Every original trap path either stops in the FFI or reaches its actual
raise; arbitrary FFI returns cannot make trap_with return normally. -/
theorem never_returns : NoReturn.Never body := by
  simp only [body, Guest.Software.guestFn_trap_with, progToHOL]
  repeat first | apply NoReturn.sequence | exact NoReturn.shared_store _ _ _ | exact NoReturn.external _ _ _ _ _ | exact NoReturn.raise _ _

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (word : BitVec 64)
    (known : codeFn (ofString "trap_with") = some (formals, body, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), lookupCodeHOLFinite codeFn (ofString "trap_with") (values word) = some (body, callee, .one) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values word).length ∧
      ((formals.zip (values word)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals, values, shapeOfHOLExact, shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "trap_with") (values word) = some (body, rawLocals word, .one) := by
    simp only [lookupCodeHOLExact, known, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, called, _⟩ := WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee, called⟩

theorem call_not_normal {F : Type} (source post : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64)) (word : BitVec 64)
    (known : source.code.lookup (ofString "trap_with") = some (formals, body, .one))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values word)) :
    evaluateHOLFiniteState source (.call (some (none, none)) (ofString "trap_with") arguments) ≠ (none, post) := by
  intro normal
  obtain ⟨callee, called⟩ := environment source.code.lookup word known
  obtain ⟨_, target, returned, actual⟩ := CallNormal.ignored_callee_return source post (ofString "trap_with") arguments (values word) body callee .one args called normal
  exact never_returns (callEntryStateHOLFinite source callee) returned (congrArg Prod.fst actual)

end InitECandidate.Solver.Input.Trap

#print axioms InitECandidate.Solver.Input.Trap.never_returns
#print axioms InitECandidate.Solver.Input.Trap.environment
#print axioms InitECandidate.Solver.Input.Trap.call_not_normal
