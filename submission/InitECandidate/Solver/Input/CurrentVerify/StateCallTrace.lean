import InitECandidate.Solver.Input.CurrentVerify.StateCallProgram
import InitECandidate.Solver.Input.LoadOneWord
import InitECandidate.Solver.Input.IgnoredSequenceObserve

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def StateInitResumes (source target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (childResult outcome : Option (PanSemResultExact 64)) : Prop :=
  post.clock=target.clock ∨ ∃ value,childResult=some (.returned value) ∧ shapeEqHOL (shapeOfHOLExact value) .one=true ∧
    evaluateHOLFiniteState {target with locals:=source.locals} afterStateInit=(outcome,post)

/-- The actual scalar root read supplies the third dynamic argument. All
callee outcomes are observed; only its genuine return resumes the real tail. -/
theorem state_init_call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (nodes codes : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (codeCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterCodes=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ root entry target childResult,
      QueryBranch.eval source stateRootExpression=some (.val (.word root)) ∧
      LocalEffects.erase entry=LocalEffects.erase source ∧ entry.clock=source.clock-1 ∧
      entry.locals.lookup (ofString "nodedb")=some (.val (.word nodes)) ∧
      entry.locals.lookup (ofString "state_root")=some (.val (.word root)) ∧
      entry.locals.lookup (ofString "codedb")=some (.val (.word codes)) ∧
      evaluateHOLFiniteState entry Mpt.StateInit.body=(childResult,target) ∧ StateInitResumes source target post childResult outcome := by
  have nodesRead : QueryBranch.eval source (QueryBranch.localVar "nodedb")=some (.val (.word nodes)) := by
    simp [QueryBranch.eval,QueryBranch.localVar,evalHOLExact,toExact,nodeCell]
  have codesRead : QueryBranch.eval source (QueryBranch.localVar "codedb")=some (.val (.word codes)) := by
    simp [QueryBranch.eval,QueryBranch.localVar,evalHOLExact,toExact,codeCell]
  rw [state_init_shape] at run
  cases rootRead : QueryBranch.eval source stateRootExpression with
  | none =>
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) stateInitArguments=none := by
      simp only [QueryBranch.eval] at nodesRead rootRead codesRead
      simp [stateInitArguments,evalListHOLFinite,evalListHOLExact,nodesRead,rootRead,codesRead]
    rw [stateInitCall,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call,args] at run
    have endpoint : post=source := (congrArg Prod.snd run).symm
    exact Or.inl (by rw [endpoint]; omega)
  | some value =>
    obtain ⟨root,valueEq⟩ := load_one_word source (.op .add [QueryBranch.localVar "parent",.const 32#64]) value rootRead
    rw [valueEq] at rootRead
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) stateInitArguments=some (Mpt.StateInit.values nodes root codes) := by
      have read:=rootRead
      simp only [QueryBranch.eval] at nodesRead read codesRead
      simp [stateInitArguments,Mpt.StateInit.values,evalListHOLFinite,evalListHOLExact,nodesRead,read,codesRead]
    obtain ⟨callee,called,nodesCell,rootCell,codesCell⟩ := Mpt.StateInit.environment source.code.lookup nodes root codes (Mpt.StateInit.original_code source.code installed)
    rcases CallNormal.ignored_sequence_observe source post (ofString "state_init") stateInitArguments _ Mpt.StateInit.body afterStateInit callee .one args called outcome run with stopped|observed
    · exact Or.inl stopped
    · obtain ⟨childResult,target,funded,childRun,remaining⟩ := observed
      exact Or.inr ⟨root,callEntryStateHOLFinite source callee,target,childResult,congrArg Option.some valueEq,rfl,rfl,nodesCell,rootCell,codesCell,childRun,remaining⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.state_init_call_trace
