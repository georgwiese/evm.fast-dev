import InitECandidate.Solver.Input.CallPrefixExecution
import InitECandidate.Solver.Input.NoReturnAtoms

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A small syntactic class of lexical actions which retain a selected
local and cannot themselves return from the enclosing function. -/
def Action.keeps (action : Action) (key : MlS) : Bool :=
  match action with
  | .declare name _ _ | .scoped name _ _ _ => decide (name ≠ key)
  | .command (.store _ _) | .command (.storeByte _ _) | .command .skip => true
  | .command _ => false

theorem Reaches.keeps {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action}
    (reached : Reaches source action target) (key : MlS) (kept : action.keeps key = true) :
    target.locals.lookup key = source.locals.lookup key := by
  cases reached with
  | declare name shape expression value read checked =>
    have different : name ≠ key := of_decide_eq_true kept
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different]
  | «scoped» name shape function arguments values body callee returnShape returned target args called funded run checked =>
    have different : name ≠ key := of_decide_eq_true kept
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different]
  | command target command run =>
    cases command with
    | skip =>
      have same : source = target := by simpa only [evaluateHOLFiniteState_skip] using congrArg Prod.snd run
      rw [← same]
    | store address value =>
      have info := (show LocalPrefix key (.store address value) from .store _ _).summary_full source
      unfold LocalSummary at info
      rw [run] at info
      exact info.1 rfl
    | storeByte address value =>
      have info := byte_store_local key address value source
      unfold LocalSummary at info
      rw [run] at info
      exact info.1 rfl
    | _ => cases kept

theorem Execution.keeps {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) (key : MlS)
    (kept : ∀ action ∈ actions, action.keeps key = true) : target.locals.lookup key = source.locals.lookup key := by
  induction execution with
  | done source => rfl
  | @step source middle target action rest first next ih =>
    exact (ih (fun child member => kept child (List.mem_cons_of_mem _ member))).trans
      (first.keeps key (kept action (by simp)))

/-- The literal safe prefix cannot supply an enclosing return. This fact
allows a genuine returned body to expose its real reached lexical actions. -/
theorem kept_never (actions : List Action) (key : MlS)
    (kept : ∀ action ∈ actions, action.keeps key = true) : NoReturn.Never (program actions .skip) := by
  induction actions with
  | nil => exact NoReturn.skip
  | cons action rest ih =>
    have current := kept action (by simp)
    have tail : NoReturn.Never (program rest .skip) := ih (fun child member => kept child (List.mem_cons_of_mem _ member))
    cases action with
    | declare name shape expression => exact @NoReturn.declared name shape expression _ (@tail)
    | «scoped» name shape function arguments => exact @NoReturn.scoped_call name shape function arguments _ (@tail)
    | command command =>
      cases command with
      | skip => exact @NoReturn.sequence _ _ (@NoReturn.skip) (@tail)
      | store address value => exact @NoReturn.sequence _ _ (@NoReturn.store address value) (@tail)
      | storeByte address value => exact @NoReturn.sequence _ _ (@NoReturn.store_byte address value) (@tail)
      | _ => cases current

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.keeps
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.keeps
#print axioms InitECandidate.Solver.Input.CallPrefix.kept_never
