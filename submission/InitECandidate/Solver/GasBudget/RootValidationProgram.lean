import InitECandidate.Solver.GasBudget.RootValidationGuard
import InitECandidate.Solver.Input.PureGuard

namespace InitECandidate.Solver.GasBudget.RootValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

 def body : ProgHOL 64 := match Guest.guestFn_validate_transaction with
  | .function fn => progToHOL fn.body
  | _ => .skip

def throwWhen (test : ExpHOL 64) (errorCode : BitVec 64) : ProgHOL 64 :=
  .ite test (.raise (ofString "TxErr") (.const errorCode)) .skip

def gasGuard : ProgHOL 64 := throwWhen (.cmp .lower (.const 4294967295#64) (localVar "gas")) 66#64
def totalGuard : ProgHOL 64 := throwWhen (.cmp .lower (localVar "gas") (.op .add [field 0, field 1])) 60#64
def floorGasGuard : ProgHOL 64 := throwWhen (.cmp .lower (localVar "gas") (field 2)) 61#64
def codeGuard : ProgHOL 64 :=
  .ite (.cmp .equal (.load .one (addConst (localVar "tx") 152#64)) (.const 0#64))
    (throwWhen (.cmp .lower (.const 131072#64) (.load .one (addConst (localVar "tx") 200#64))) 62#64) .skip

def fitsGuard : ProgHOL 64 := throwWhen (.cmp .equal (localVar "fits") (.const 0#64)) 65#64
def nonceGuard : ProgHOL 64 := throwWhen
  (.cmp .equal (.rfield 0 (localVar "nonce")) (.op .sub [.const 0#64, .const 1#64])) 65#64

def nonceShape : ShapeHOL := .comb [.one, .one, .one, .one]
def nonceExpression : ExpHOL 64 := .load nonceShape (addConst (localVar "tx") 16#64)
def fitsBody : ProgHOL 64 := .seq fitsGuard (.seq nonceGuard (.return (localVar "ic")))
def nonceBody : ProgHOL 64 := .dec (ofString "nonce") nonceShape nonceExpression
  (.decCall (ofString "fits") .one (ofString "u256_fits_word") [localVar "nonce"] fitsBody)
def capBody : ProgHOL 64 := .seq (guard 0 63#64) (.seq (guard 2 64#64) nonceBody)
def gasBody : ProgHOL 64 := .seq gasGuard (.seq totalGuard (.seq floorGasGuard (.seq codeGuard capBody)))
def gasExpression : ExpHOL 64 := .load .one (addConst (localVar "tx") 144#64)
def intrinsicBody : ProgHOL 64 := .dec (ofString "gas") .one gasExpression gasBody
def intrinsicShape : ShapeHOL := .comb [.one, .one, .one]

theorem body_shape : body = .decCall (ofString "ic") intrinsicShape (ofString "calculate_intrinsic_cost")
    [localVar "tx", localVar "sender"] intrinsicBody := by
  simp only [body, Guest.guestFn_validate_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, intrinsicShape, intrinsicBody, gasExpression,
    gasBody, gasGuard, totalGuard, floorGasGuard, codeGuard, capBody, guard, condition,
    nonceBody, nonceShape, nonceExpression, fitsBody, fitsGuard, nonceGuard, throwWhen,
    field, localVar, addConst]

 theorem throwWhen_pure (test : ExpHOL 64) (errorCode : BitVec 64) : Input.PureGuard (throwWhen test errorCode) :=
  .ite test (.raise _ _) .skip

theorem prefix_guards_pure : Input.PureGuard gasGuard ∧ Input.PureGuard totalGuard ∧
    Input.PureGuard floorGasGuard ∧ Input.PureGuard codeGuard :=
  ⟨throwWhen_pure _ _, throwWhen_pure _ _, throwWhen_pure _ _,
    .ite _ (throwWhen_pure _ _) .skip⟩

theorem cap_guard_pure (index : Nat) (errorCode : BitVec 64) : Input.PureGuard (guard index errorCode) :=
  .ite _ (.raise _ _) .skip

theorem nonce_guards_pure : Input.PureGuard fitsGuard ∧ Input.PureGuard nonceGuard :=
  ⟨throwWhen_pure _ _, throwWhen_pure _ _⟩

end InitECandidate.Solver.GasBudget.RootValidation

#print axioms InitECandidate.Solver.GasBudget.RootValidation.body_shape
#print axioms InitECandidate.Solver.GasBudget.RootValidation.prefix_guards_pure
#print axioms InitECandidate.Solver.GasBudget.RootValidation.cap_guard_pure
#print axioms InitECandidate.Solver.GasBudget.RootValidation.nonce_guards_pure
