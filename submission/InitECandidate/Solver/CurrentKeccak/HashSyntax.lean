import InitECandidate.Solver.CurrentKeccak.AbsorbSyntax
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_keccak256 with | .function fn => progToHOL fn.body | _ => .skip
def condition : ExpHOL 64 := .cmp .notLower (localVar "n") (addConst (localVar "i") 136#64)
def blockArguments : List (ExpHOL 64) := [localVar "stp", .op .add [localVar "p", localVar "i"]]
def blockBody : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "keccak_absorb_block") blockArguments) ((.assign .local (ofString "i") (.op .add [localVar "i",.const 136#64])))
def blocks : ProgHOL 64 := .while condition blockBody
def afterBlocks : ProgHOL 64 := match body with
  | .dec _ _ _ (.seq _ (.dec _ _ _ (.seq _ rest))) => rest
  | _ => .skip

theorem body_shape : body = .dec (ofString "stp") .one (.var .global (ofString "keccak_st"))
    (.seq (.call (some (none,none)) (ofString "memzero") [localVar "stp",.const 200#64])
      (.dec (ofString "i") .one (.const 0#64) (.seq blocks afterBlocks))) := by
  simp only [body,Guest.Software.guestFn_keccak256,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    blocks,condition,blockBody,blockArguments,localVar,addConst,afterBlocks]
  rfl

def formals : List (MlS × ShapeHOL) := [(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)]
def values (pointer out : BitVec 64) (length : Nat) : List (ValueHOL 64) :=
  [.val (.word pointer),.val (.word (BitVec.ofNat 64 length)),.val (.word out)]
def rawLocals (pointer out : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out))
  else if name=ofString "n" then some (.val (.word (BitVec.ofNat 64 length)))
  else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (pointer out : BitVec 64) (length : Nat)
    (code : codeFn (ofString "keccak256")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "keccak256") (values pointer out length)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) ∧
      callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values pointer out length).length ∧
      ((formals.zip (values pointer out length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "keccak256") (values pointer out length)=some (body,rawLocals pointer out length,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,lookup,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,lookup,?_,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,ofString]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "keccak256")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 92 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_keccak256) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.Software.guestFn_keccak256,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.body_shape
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.environment
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.original_code
