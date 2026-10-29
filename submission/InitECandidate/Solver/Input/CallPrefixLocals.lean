import InitECandidate.Solver.Input.CallPrefixExecution
import InitECandidate.Solver.Input.PureDecision
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A reached lexical action retains this actual caller binding. -/
def KeepsLocal (key : MlS) (action : Action) : Prop:=
  ∀ source target,Reaches source action target→target.locals.lookup key=source.locals.lookup key

theorem KeepsLocal.declared (key name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (other : key≠name) :
    KeepsLocal key (.declare name shape expression) := by
  intro source target actual
  cases actual with
  | declare name shape expression value read checked=>simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]

theorem KeepsLocal.scoped (key name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (other : key≠name) :
    KeepsLocal key (.scoped name shape function arguments) := by
  intro source target actual
  cases actual with
  | «scoped» name shape function arguments values body callee returnShape returned target args called funded run checked=>
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]

theorem KeepsLocal.decision (key : MlS) (program : ProgHOL 64) (pure : PureDecision program) : KeepsLocal key (.command program) := by
  intro source target actual
  cases actual with
  | command target command run=>
    have summary:=pure.summary source
    rw [run] at summary
    have same:=summary.1 rfl
    dsimp only at same
    rw [same]

theorem KeepsLocal.global_assignment (key name : MlS) (expression : ExpHOL 64) : KeepsLocal key (.command (.assign .global name expression)) := by
  intro source target actual
  cases actual with
  | command target command run=>
    have safe : LocalPrefix key (.assign .global name expression):=.globalAssign _ _
    have summary:=safe.summary source
    rw [run] at summary
    exact summary.1 rfl

theorem Execution.keeps_local {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (actual : Execution source actions target) (key : MlS) (safe : ∀ action∈actions,KeepsLocal key action) :
    target.locals.lookup key=source.locals.lookup key := by
  induction actual with
  | done source=>rfl
  | @step source middle target action rest first next ih=>
    exact (ih (fun child member=>safe child (List.mem_cons_of_mem _ member))).trans (safe action (by simp) source middle first)

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.KeepsLocal.declared
#print axioms InitECandidate.Solver.Input.CallPrefix.KeepsLocal.scoped
#print axioms InitECandidate.Solver.Input.CallPrefix.KeepsLocal.decision
#print axioms InitECandidate.Solver.Input.CallPrefix.KeepsLocal.global_assignment
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.keeps_local
