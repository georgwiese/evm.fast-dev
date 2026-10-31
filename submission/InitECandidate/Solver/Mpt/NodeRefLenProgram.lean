import InitECandidate.Solver.Mpt.NodeNeedsRlp
import InitECandidate.Solver.Mpt.FailGuardReturn

namespace InitECandidate.Solver.Mpt.NodeRefLen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_node_ref_len with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "child",.one)]
def readAt (offset : Nat) : ExpHOL 64:=NodeNeedsRlp.readAt offset
def cacheTest : ExpHOL 64:=.cmp .equal (readAt 8) (.const 0#64)
def cacheGuard : ProgHOL 64:=.ite cacheTest (.call (some (none,none)) (ofString "mpt_fail") [.const 13#64]) .skip
def lengthTail : ProgHOL 64:=.seq (.ite (.cmp .lower (localVar "rl") (.const 32#64)) (.return (localVar "rl")) .skip) (.return (.const 33#64))
def afterCache : ProgHOL 64:=.dec (ofString "rl") .one (readAt 16) lengthTail
def checkedTail : ProgHOL 64:=.seq cacheGuard afterCache

theorem body_shape : body=.seq (.ite (.cmp .equal (localVar "child") (.const 0#64)) (.return (.const 1#64)) .skip)
    (.seq (.ite (.cmp .equal (readAt 0) (.const 0#64)) (.return (.const 33#64)) .skip) checkedTail) := by
  simp only [body,Guest.Software.guestFn_node_ref_len,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,readAt,NodeNeedsRlp.readAt,cacheTest,cacheGuard,checkedTail,afterCache,lengthTail,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "node_ref_len")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 261 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_node_ref_len) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_node_ref_len,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (child : BitVec 64)
    (known : codeFn (ofString "node_ref_len")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "node_ref_len") [.val (.word child)]=some (body,callee,.one) ∧
      callee.lookup (ofString "child")=some (.val (.word child)) :=
  Input.word_environment codeFn (ofString "node_ref_len") (ofString "child") body .one child known

theorem length_tail_cost (code) : Input.ClockCost.Bound code lengthTail 0 := by
  exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.conditional code _ _ _ 0 0 (Input.ClockCost.returned code _) (Input.ClockCost.skip code)) (Input.ClockCost.returned code _)

/-- Every outcome costs at most the one possible failure-helper call.
No cache validity or successful return is assumed to price this helper. -/
theorem body_cost (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code body 1 := by
  have stopped (test : ExpHOL 64) (word : BitVec 64) : Input.ClockCost.Bound code (.ite test (.return (.const word)) .skip) 0:=
    Input.ClockCost.conditional code _ _ _ 0 0 (Input.ClockCost.returned code _) (Input.ClockCost.skip code)
  have guarded : Input.ClockCost.Bound code cacheGuard 1:=Input.ClockCost.conditional code _ _ _ 1 1 (Fail.call_price code installed _) (by
    intro source same; have pure:=Input.ClockCost.skip code source same; omega)
  have after : Input.ClockCost.Bound code afterCache 0:=Input.ClockCost.declared code _ _ _ _ 0 (length_tail_cost code)
  rw [body_shape]
  exact Input.ClockCost.sequence code _ _ 0 1 (stopped _ _) (Input.ClockCost.sequence code _ _ 0 1 (stopped _ _)
    (Input.ClockCost.sequence code _ _ 1 0 guarded after))

theorem readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code body := by
  rw [body_shape]
  unfold checkedTail cacheGuard afterCache lengthTail
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.conditional
    | apply Input.LocalEffects.declared
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code
    | exact Input.LocalEffects.call_body code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one (Fail.original_code code installed) (Fail.readonly code)

end InitECandidate.Solver.Mpt.NodeRefLen

#print axioms InitECandidate.Solver.Mpt.NodeRefLen.body_shape
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.original_code
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.environment
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.length_tail_cost
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.body_cost
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.readonly
