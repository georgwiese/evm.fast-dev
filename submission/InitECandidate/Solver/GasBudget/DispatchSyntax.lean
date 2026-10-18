import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.TrapNoReturn

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Guard where
  | equal (bound : Nat)
  | lower (bound : Nat)

def Guard.expression : Guard → ExpHOL 64
  | .equal bound => .cmp .equal (localVar "op") (.const (BitVec.ofNat 64 bound))
  | .lower bound => .cmp .lower (localVar "op") (.const (BitVec.ofNat 64 bound))

def Guard.test (guard : Guard) (op : BitVec 64) : Bool := match guard with
  | .equal bound => op == BitVec.ofNat 64 bound
  | .lower bound => decide (op < BitVec.ofNat 64 bound)

theorem Guard.read (guard : Guard) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op))) :
    eval source guard.expression = some (.val (.word (if guard.test op then 1#64 else 0#64))) := by
  cases guard <;> simp [Guard.expression, Guard.test, eval, evalHOLExact, localVar, toExact, opLocal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

inductive Action where
  | skip
  | returned
  | failed
  | invoke (function : String) (arguments : List (ExpHOL 64))

def Action.program : Action → ProgHOL 64
  | .skip => .skip
  | .returned => .return (.const 0#64)
  | .failed => .raise (ofString "EvmErr") (.const 5#64)
  | .invoke function arguments => .seq (.call (some (none, none)) (ofString function) arguments) (.return (.const 0#64))

/-- Every selected action except skip finishes this dispatcher body, whether
its real callee returns, throws, fails or times out. -/
theorem Action.not_none (action : Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (terminal : action ≠ .skip) :
    (evaluateHOLFiniteState source action.program).1 ≠ none := by
  cases action with
  | skip => exact (terminal rfl).elim
  | returned => simp [Action.program, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  | failed =>
    rw [Action.program, evaluateHOLFiniteState_raise]
    simp only [evalHOLExact]
    split <;> simp_all
    all_goals split <;> simp
  | invoke function arguments =>
    rw [Action.program, evaluateHOLFiniteState_seq_line780]
    generalize computed : evaluateHOLFiniteState source (.call (some (none, none)) (ofString function) arguments) = output
    obtain ⟨result, target⟩ := output
    cases result with
    | none => simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
    | some result => simp

inductive Syntax where
  | action (action : Action)
  | branch (guard : Guard) (yes no : Syntax)
  | seq (first second : Syntax)

def Syntax.program : Syntax → ProgHOL 64
  | .action leaf => leaf.program
  | .branch guard yes no => .ite guard.expression yes.program no.program
  | .seq first second => .seq first.program second.program

def Syntax.choose (op : BitVec 64) : Syntax → Action
  | .action leaf => leaf
  | .branch guard yes no => if guard.test op then yes.choose op else no.choose op
  | .seq first second => match first.choose op with | .skip => second.choose op | other => other

/-- Selecting the actual read-only opcode guards preserves the entire
original evaluation and state, at every clock and for every callee outcome.
The exact original dispatcher is connected to this tree separately. -/
theorem Syntax.choose_execution (tree : Syntax) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op))) :
    evaluateHOLFiniteState source tree.program = evaluateHOLFiniteState source (tree.choose op).program := by
  induction tree with
  | action leaf => rfl
  | branch guard yes no yesIH noIH =>
    have read := guard.read source op opLocal
    simp only [eval] at read
    rw [Syntax.program, evaluateHOLFiniteState_ite, read]
    cases test : guard.test op <;> simp only [test, Bool.false_eq_true, ↓reduceIte, Syntax.choose]
    · simpa using noIH
    · simpa using yesIH
  | seq first second firstIH secondIH =>
    rw [Syntax.program, evaluateHOLFiniteState_seq_line780, firstIH]
    cases selected : first.choose op with
    | skip =>
      simpa only [Action.program, evaluateHOLFiniteState_skip, Syntax.choose, selected] using secondIH
    | returned =>
      have terminal := Action.not_none .returned source (by intro impossible; cases impossible)
      generalize run : evaluateHOLFiniteState source Action.returned.program = output at terminal ⊢
      obtain ⟨result, target⟩ := output
      cases result with
      | none => exact (terminal rfl).elim
      | some result => simp [Syntax.choose, selected, ← run]
    | failed =>
      have terminal := Action.not_none .failed source (by intro impossible; cases impossible)
      generalize run : evaluateHOLFiniteState source Action.failed.program = output at terminal ⊢
      obtain ⟨result, target⟩ := output
      cases result with
      | none => exact (terminal rfl).elim
      | some result => simp [Syntax.choose, selected, ← run]
    | invoke function arguments =>
      have terminal := Action.not_none (.invoke function arguments) source (by intro impossible; cases impossible)
      generalize run : evaluateHOLFiniteState source (Action.invoke function arguments).program = output at terminal ⊢
      obtain ⟨result, target⟩ := output
      cases result with
      | none => exact (terminal rfl).elim
      | some result => simp [Syntax.choose, selected, ← run]

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.Guard.read
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.Action.not_none
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.Syntax.choose_execution
