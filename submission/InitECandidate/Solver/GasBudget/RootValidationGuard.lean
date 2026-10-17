import InitECandidate.Solver.GasBudget.RootExecution
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.GasBudget.RootValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def field (index : Nat) : ExpHOL 64 := .rfield index (localVar "ic")
def condition (index : Nat) : ExpHOL 64 := .cmp .lower (.const 16777216#64) (field index)
def guard (index : Nat) (errorCode : BitVec 64) : ProgHOL 64 :=
  .ite (condition index) (.raise (ofString "TxErr") (.const errorCode)) .skip

def sites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.ite _ (.raise name (.const errorCode)) .skip) =>
      if name = ofString "TxErr" ∧ (errorCode = 63#64 ∨ errorCode = 64#64) then [code] else []
  | .seq a b | .ite _ a b => sites a ++ sites b
  | .dec _ _ _ body | .decCall _ _ _ _ body | .while _ body => sites body
  | _ => []
def selected : List (ProgHOL 64) := match Guest.guestFn_validate_transaction with
  | .function fn => sites (progToHOL fn.body)
  | _ => []

set_option maxRecDepth 10000 in
theorem actual_guards : selected = [guard 0 63#64, guard 2 64#64] := by
  simp only [selected, Guest.guestFn_validate_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, sites, ↓reduceIte,
    List.nil_append, List.cons_append, List.append_nil, guard, condition, field, localVar]
  rfl

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (value : BitVec 64)
    (read : eval source (field index) = some (.val (.word value))) :
    eval source (condition index) = some (.val (.word (if 16777216#64 < value then 1#64 else 0#64))) := by
  simp only [eval] at read ⊢
  rw [condition, evalHOLExact, read]
  simp [evalHOLExact, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- Both actual cap guards either continue unchanged or raise their exact
TxErr without spending any source clock or entering the following body. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (errorCode value : BitVec 64)
    (read : eval source (field index) = some (.val (.word value)))
    (shape : source.eshapes.lookup (ofString "TxErr") = some .one) :
    evaluateHOLFiniteState source (guard index errorCode) =
      if 16777216#64 < value then
        (some (.exception (ofString "TxErr") (.val (.word errorCode))), emptyLocalsHOLFinite source)
      else (none, source) := by
  have test := condition_read source index value read
  simp only [eval] at test
  rw [guard, evaluateHOLFiniteState_ite, test]
  by_cases over : 16777216#64 < value
  all_goals simp [over, evaluateHOLFiniteState_raise, shape, evalHOLExact,
    shapeOfHOLExact, sizeOfShapeWithContextHOL]

/-- A normal return past a real cap guard derives its bound. Failure cannot
be masked by a later continuation, including when the initial clock is zero. -/
theorem normal_cap (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (index : Nat) (errorCode value : BitVec 64) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (read : eval source (field index) = some (.val (.word value)))
    (shape : source.eshapes.lookup (ofString "TxErr") = some .one)
    (run : evaluateHOLFiniteState source (.seq (guard index errorCode) continuation) =
      (some (.returned returned), post)) : value.toNat ≤ 16777216 := by
  by_contra larger
  have over : 16777216#64 < value := by change 16777216 < value.toNat; omega
  have failed := execute source index errorCode value read shape
  rw [if_pos over] at failed
  have stopped := WitnessRadix.StateSteps.stopped_sequence source (emptyLocalsHOLFinite source)
    (guard index errorCode) continuation (.exception (ofString "TxErr") (.val (.word errorCode))) failed (Nat.le_refl _)
  rw [stopped] at run
  cases run

/-- A malformed intrinsic projection makes the real comparison fail before
any continuation can execute. -/
theorem condition_error (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (observed : Option (ValueHOL 64)) (read : eval source (field index) = observed)
    (invalid : ∀ word : BitVec 64, observed ≠ some (.val (.word word))) :
    eval source (condition index) = none := by
  simp only [eval] at read ⊢
  rw [condition, evalHOLExact, read]
  cases observed with
  | none => simp [evalHOLExact]
  | some value =>
    cases value with
    | val payload =>
      cases payload with
      | word word => exact False.elim (invalid word rfl)
    | rStruct fields => simp [evalHOLExact]
    | nStruct name fields => simp [evalHOLExact]

/-- A genuine normal return derives both a word-valued intrinsic projection
and its cap; neither successful field decoding nor the cap is assumed. -/
theorem normal_field (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (index : Nat) (errorCode : BitVec 64) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (shape : source.eshapes.lookup (ofString "TxErr") = some .one)
    (run : evaluateHOLFiniteState source (.seq (guard index errorCode) continuation) =
      (some (.returned returned), post)) :
    ∃ word : BitVec 64, eval source (field index) = some (.val (.word word)) ∧ word.toNat ≤ 16777216 := by
  classical
  by_cases found : ∃ word : BitVec 64, eval source (field index) = some (.val (.word word))
  · obtain ⟨word, read⟩ := found
    exact ⟨word, read, normal_cap source post index errorCode word continuation returned read shape run⟩
  · have invalid : ∀ word : BitVec 64, eval source (field index) ≠ some (.val (.word word)) := by
      intro word read
      exact found ⟨word, read⟩
    have test := condition_error source index (eval source (field index)) rfl invalid
    simp only [eval] at test
    have failed : evaluateHOLFiniteState source (guard index errorCode) = (some .error, source) := by
      rw [guard, evaluateHOLFiniteState_ite, test]
    have stopped := WitnessRadix.StateSteps.stopped_sequence source source (guard index errorCode)
      continuation .error failed (Nat.le_refl _)
    rw [stopped] at run
    cases run

end InitECandidate.Solver.GasBudget.RootValidation

#print axioms InitECandidate.Solver.GasBudget.RootValidation.actual_guards
#print axioms InitECandidate.Solver.GasBudget.RootValidation.condition_read
#print axioms InitECandidate.Solver.GasBudget.RootValidation.execute
#print axioms InitECandidate.Solver.GasBudget.RootValidation.normal_cap

#print axioms InitECandidate.Solver.GasBudget.RootValidation.condition_error
#print axioms InitECandidate.Solver.GasBudget.RootValidation.normal_field
