import InitECandidate.Solver.Mpt.StateInitProgram
import InitECandidate.Solver.Mpt.WitnessDecodeRootEnvironment
import InitECandidate.Solver.Input.ScopedCallObserve

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def RootResumes (source target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (childResult outcome : Option (PanSemResultExact 64)) : Prop :=
  post.clock=target.clock ∨ ∃ returned inner,
    childResult=some (.returned returned) ∧ shapeEqHOL (shapeOfHOLExact returned) .one=true ∧
    evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target "root" returned) afterRoot=(outcome,inner) ∧
    post=QueryBranch.restore source "root" inner

/-- Observe the actual original root-materializer invocation, including
every child outcome and its genuine checked continuation. -/
theorem root_call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (nodes root : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source rootCall=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ entry target childResult,
      Input.LocalEffects.erase entry=Input.LocalEffects.erase source ∧ entry.clock=source.clock-1 ∧
      entry.locals.lookup (ofString "db")=some (.val (.word nodes)) ∧ entry.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      evaluateHOLFiniteState entry WitnessDecodeRoot.body=(childResult,target) ∧ RootResumes source target post childResult outcome := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) rootArguments=
      some (WitnessDecodeRoot.values nodes root) := by
    simp [rootArguments,QueryBranch.localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,nodeCell,rootCell,WitnessDecodeRoot.values]
  obtain ⟨callee,called,dbCell,hashCell⟩ := WitnessDecodeRoot.environment source.code.lookup nodes root
    (WitnessDecodeRoot.original_code source.code installed)
  rw [shapes.2.2.2.2] at run
  rcases Input.CallNormal.scoped_observe source post "root" .one (ofString "decode_witness_to_mpt") rootArguments _
      WitnessDecodeRoot.body afterRoot callee .one args called outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨childResult,target,funded,childRun,resumes⟩ := reached
    refine Or.inr ⟨callEntryStateHOLFinite source callee,target,childResult,rfl,rfl,dbCell,hashCell,childRun,?_⟩
    rcases resumes with stopped|normal
    · exact Or.inl stopped
    · obtain ⟨returned,inner,returnedEq,shape,continued,endpoint⟩ := normal
      have checked : shapeEqHOL (shapeOfHOLExact returned) .one=true := by simpa using shape
      exact Or.inr ⟨returned,inner,returnedEq,checked,continued,endpoint⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.root_call_trace
