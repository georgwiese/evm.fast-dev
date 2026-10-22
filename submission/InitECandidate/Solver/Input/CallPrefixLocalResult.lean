import InitECandidate.Solver.Input.CallPrefixExecution

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def Action.avoids (key : MlS) : Action→Prop
  | .declare name _ _ | .scoped name _ _ _=>name≠key
  | .command _=>True

/-- Lexical prefix restoration only restores the prefix's own binders.
Every other local at the actual end agrees with the reached remainder. -/
theorem Reaches.local_result {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action}
    (reached : Reaches source action target) (key : MlS) (other : action.avoids key) (tail : ProgHOL 64) :
    (evaluateHOLFiniteState source (program [action] tail)).2.locals.lookup key=
      (evaluateHOLFiniteState target tail).2.locals.lookup key := by
  cases reached with
  | declare name shape expression value read checked=>
    simp only [WitnessRadix.QueryBranch.eval] at read
    rw [program,evaluateHOLFiniteState_dec_total]
    simp only [read,if_pos checked,program]
    rw [lookup_resVarEq_toExact]
    change name≠key at other
    cases source.locals.lookup name <;> simp [resVarHOLExact,FUPDATE,FDOMSUB,other,Ne.symm other]
  | «scoped» name shape function arguments values body callee returnShape returned target args called funded run checked=>
    rw [program,evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp only [args,called,if_neg funded,run,if_pos checked,program]
    rw [lookup_resVarEq_toExact]
    change name≠key at other
    cases source.locals.lookup name <;> simp [resVarHOLExact,FUPDATE,FDOMSUB,other,Ne.symm other]
  | command target command run=>rw [program,evaluateHOLFiniteState_seq_line780,run];rfl

theorem Execution.local_result {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List Action}
    (execution : Execution source actions target) (key : MlS) (other : ∀ action∈actions,action.avoids key) (tail : ProgHOL 64) :
    (evaluateHOLFiniteState source (program actions tail)).2.locals.lookup key=
      (evaluateHOLFiniteState target tail).2.locals.lookup key := by
  induction execution with
  | done source=>rfl
  | @step source middle target action rest first next ih=>
    rw [program_cons]
    exact (first.local_result key (other action (by simp)) _).trans
      (ih (by intro action member; exact other action (by simp [member])))

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.local_result
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.local_result
