import InitECandidate.Solver.Input.MainBnAccelImage
import InitECandidate.Solver.Input.MainBnAccelInitialization
import InitECandidate.Solver.Input.RlpWrite.U256Load
import InitECandidate.Solver.Input.BnArithmeticOracle

namespace InitECandidate.Solver.Input.BnModmul
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
abbrev Words := RlpWrite.U256Value.Words

def body : ProgHOL 64 := match Guest.guestFn_bn254_accel_modmul with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "a",RlpWrite.U256Value.tupleShape),(ofString "b",RlpWrite.U256Value.tupleShape)]
def initialization : ProgHOL 64 := .call (some (none,none)) (ofString "bn254_accel_init") []
def storeA : ProgHOL 64 := .store (.var .global (ofString "bn_accel_a")) (.var .local (ofString "a"))
def storeB : ProgHOL 64 := .store (.var .global (ofString "bn_accel_b")) (.var .local (ofString "b"))
def external : ProgHOL 64 := .extCall (ofString "bn_arith256") (.var .global (ofString "bn_accel_params")) (.const 0#64)
  (.var .global (ofString "bn_accel_params")) (.const 160#64)
def returned : ProgHOL 64 := .return (.load RlpWrite.U256Value.tupleShape (.var .global (ofString "bn_accel_d")))
def afterStores : ProgHOL 64 := .seq external returned
def afterInitialization : ProgHOL 64 := .seq storeA (.seq storeB afterStores)
def fqBody : ProgHOL 64 := match Guest.guestFn_fq_mul with | .function fn => progToHOL fn.body | _ => .skip

theorem body_shape : body = .seq initialization afterInitialization := by
  simp only [body,initialization,afterInitialization,storeA,storeB,afterStores,external,returned,RlpWrite.U256Value.tupleShape,
    Guest.guestFn_bn254_accel_modmul,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem fq_body_shape : fqBody = .call none (ofString "bn254_accel_modmul") [.var .local (ofString "a"),.var .local (ofString "b")] := by
  simp only [fqBody,Guest.guestFn_fq_mul,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "bn254_accel_modmul") = some (formals,body,RlpWrite.U256Value.tupleShape) := by
  have checked := OriginalCode.indexed code installed 593 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_bn254_accel_modmul) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,RlpWrite.U256Value.tupleShape,Guest.guestFn_bn254_accel_modmul,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem fq_original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "fq_mul") = some (formals,fqBody,RlpWrite.U256Value.tupleShape) := by
  have checked := OriginalCode.indexed code installed 602 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_fq_mul) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,fqBody,formals,RlpWrite.U256Value.tupleShape,Guest.guestFn_fq_mul,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def values (a b : Words) : List (ValueHOL 64) := [RlpWrite.U256Value.tuple a,RlpWrite.U256Value.tuple b]
def rawLocals (a b : Words) (key : MlS) : Option (ValueHOL 64) :=
  if key = ofString "b" then some (RlpWrite.U256Value.tuple b) else if key = ofString "a" then some (RlpWrite.U256Value.tuple a) else none

/-- The genuine two-quad ABI, usable by both original arithmetic entries. -/
theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (program : ProgHOL 64) (a b : Words)
    (code : codeFn name = some (formals,program,RlpWrite.U256Value.tupleShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn name (values a b) = some (program,callee,RlpWrite.U256Value.tupleShape) ∧
      callee.lookup (ofString "a") = some (RlpWrite.U256Value.tuple a) ∧ callee.lookup (ofString "b") = some (RlpWrite.U256Value.tuple b) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values a b).length ∧
      ((formals.zip (values a b)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,values,RlpWrite.U256Value.tupleShape,RlpWrite.U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true,
      show ofString "a" ≠ ofString "b" by decide]
  have raw : lookupCodeHOLExact codeFn name (values a b) = some (program,rawLocals a b,RlpWrite.U256Value.tupleShape) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "a" ≠ ofString "b" by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.BnModmul

#print axioms InitECandidate.Solver.Input.BnModmul.body_shape
#print axioms InitECandidate.Solver.Input.BnModmul.fq_body_shape
#print axioms InitECandidate.Solver.Input.BnModmul.original_code
#print axioms InitECandidate.Solver.Input.BnModmul.fq_original_code
#print axioms InitECandidate.Solver.Input.BnModmul.environment
