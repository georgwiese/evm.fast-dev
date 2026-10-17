import InitECandidate.Solver.GasBudget.Minimum
import InitECandidate.Solver.PanDeclarations

namespace InitECandidate.Solver.GasBudget.RootBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def executionExpression : ExpHOL 64 := .op .sub [localVar "gas", localVar "intrinsic_gas"]
def regularExpression : ExpHOL 64 := .op .sub [.const 16777216#64, .rfield 0 (localVar "intrinsic")]
def minArguments : List (ExpHOL 64) := [localVar "regular_budget", localVar "execution_gas"]
def reservoirExpression : ExpHOL 64 := .op .sub [localVar "execution_gas", localVar "mgas"]
def program (continuation : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "execution_gas") .one executionExpression
    (.dec (ofString "regular_budget") .one regularExpression
      (.decCall (ofString "mgas") .one (ofString "min") minArguments
        (.dec (ofString "reservoir") .one reservoirExpression continuation)))

def sites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.dec name _ _ rest) =>
      (if name = ofString "execution_gas" then [code] else []) ++ sites rest
  | .seq first second | .ite _ first second => sites first ++ sites second
  | .decCall _ _ _ _ rest | .while _ rest => sites rest
  | _ => []
def eraseContinuation : ProgHOL 64 → ProgHOL 64
  | .dec a sa ea (.dec b sb eb (.decCall c sc f es (.dec d sd ed _))) =>
      .dec a sa ea (.dec b sb eb (.decCall c sc f es (.dec d sd ed .skip)))
  | _ => .skip
def selected : ProgHOL 64 := match Guest.guestFn_process_transaction with
  | .function fn => eraseContinuation (((sites (progToHOL fn.body))[0]?).getD .skip)
  | _ => .skip

set_option maxRecDepth 10000 in
/-- The exact regular/state split in the unchanged transaction processor. -/
theorem actual_site : selected = program .skip := by
  simp only [selected, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, sites, ↓reduceIte,
    List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero,
    Option.getD_some, eraseContinuation, program, executionExpression, regularExpression,
    minArguments, reservoirExpression, localVar]
  rfl

def intrinsicValue (regular state floor : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word regular), .val (.word state), .val (.word floor)]
def executionWord (gas intrinsic : BitVec 64) : BitVec 64 := gas - intrinsic
def regularWord (intrinsic : BitVec 64) : BitVec 64 := 16777216#64 - intrinsic
def liquidWord (gas intrinsic regular : BitVec 64) : BitVec 64 :=
  Minimum.selected (regularWord regular) (executionWord gas intrinsic)
def reservoirWord (gas intrinsic regular : BitVec 64) : BitVec 64 :=
  executionWord gas intrinsic - liquidWord gas intrinsic regular

/-- The cap bounds liquid regular gas independently of reservoir magnitude.
The actual successful validation path must supply the intrinsic cap premise. -/
theorem liquid_bound (gas intrinsic regular : BitVec 64) (cap : regular.toNat ≤ 16777216) :
    (liquidWord gas intrinsic regular).toNat + regular.toNat ≤ 16777216 := by
  have fits : regular ≤ 16777216#64 := cap
  have remaining : (regularWord regular).toNat = 16777216 - regular.toNat :=
    BitVec.toNat_sub_of_le fits
  have selected := Minimum.selected_number (regularWord regular) (executionWord gas intrinsic)
  have lower := Nat.min_le_left (regularWord regular).toNat (executionWord gas intrinsic).toNat
  change (liquidWord gas intrinsic regular).toNat = _ at selected
  omega

theorem split_exact (gas intrinsic regular : BitVec 64) (funded : intrinsic ≤ gas) :
    (liquidWord gas intrinsic regular).toNat + (reservoirWord gas intrinsic regular).toNat =
      gas.toNat - intrinsic.toNat := by
  have selected := Minimum.selected_number (regularWord regular) (executionWord gas intrinsic)
  have bound := Nat.min_le_right (regularWord regular).toNat (executionWord gas intrinsic).toNat
  have order : liquidWord gas intrinsic regular ≤ executionWord gas intrinsic := by
    change (liquidWord gas intrinsic regular).toNat ≤ (executionWord gas intrinsic).toNat
    change (liquidWord gas intrinsic regular).toNat = _ at selected
    omega
  rw [reservoirWord, BitVec.toNat_sub_of_le order]
  have natOrder : (liquidWord gas intrinsic regular).toNat ≤ (executionWord gas intrinsic).toNat := order
  have amount : (executionWord gas intrinsic).toNat = gas.toNat - intrinsic.toNat := BitVec.toNat_sub_of_le funded
  omega

end InitECandidate.Solver.GasBudget.RootBudget

#print axioms InitECandidate.Solver.GasBudget.RootBudget.actual_site
#print axioms InitECandidate.Solver.GasBudget.RootBudget.liquid_bound
#print axioms InitECandidate.Solver.GasBudget.RootBudget.split_exact
