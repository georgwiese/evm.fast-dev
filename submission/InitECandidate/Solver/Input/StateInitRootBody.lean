import InitECandidate.Solver.Input.StateInitRootReady
import InitECandidate.Solver.Input.StateInitRootEntry

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Execute the original workspace prefix and observe the actual root
body. Normal root returns retain the genuine state_init continuation. -/
theorem root_body_of_state_init (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (boundary : StateInitBoundary input source) (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Mpt.StateInit.body=(outcome,post)) :
    source.clock-post.clock≤2 ∨ ∃ caller entry target childResult,
      StateInitBoundary input caller ∧ RootBoundary input entry ∧ LocalEffects.erase entry=LocalEffects.erase caller ∧
      OriginalCode.Installed entry.code ∧ OriginalScalarGlobals.Scalars entry.globals ∧
      entry.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      Rlp.Validation.Arena entry 2713714688#64 2701135872#64 ∧ Keccak256.Environment entry 2713714976#64 2713715176#64 ∧
      entry.clock=source.clock-2 ∧ evaluateHOLFiniteState entry Mpt.WitnessDecodeRoot.body=(childResult,target) ∧
      Mpt.StateInit.RootResumes caller target post childResult outcome := by
  rcases root_ready_of_entry input source post root boundary installed scalars rootCell scratch environment outcome run with stopped|ready
  · exact Or.inl stopped
  · obtain ⟨heap,nodes,codes,arena,callerData,callerInstalled,callerScalars,callerRoot,callerScratch,callerEnvironment,clock,continued⟩ := ready
    let caller:=Mpt.StateInit.ready source heap nodes root codes
    change caller.clock=source.clock-1 at clock
    rcases root_entry_of_ready input caller post root callerData callerInstalled callerScalars callerRoot callerScratch callerEnvironment outcome continued with stopped|observed
    · exact Or.inl (by omega)
    · obtain ⟨entry,target,childResult,entryData,pure,entryInstalled,entryScalars,entryRoot,entryScratch,entryEnvironment,entryClock,childRun,resumes⟩ := observed
      exact Or.inr ⟨caller,entry,target,childResult,callerData,entryData,pure,entryInstalled,entryScalars,entryRoot,entryScratch,entryEnvironment,
        by omega,childRun,resumes⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.root_body_of_state_init
