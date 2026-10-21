import InitECandidate.Solver.Input.MainRootBoundary
import InitECandidate.Solver.Mpt.StateInitRootCallTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- At the real initialized root caller, every outcome either stops at
the call or exposes original241 with both physical databases and runtime. -/
theorem root_entry_of_ready (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (boundary : StateInitBoundary input source) (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Mpt.StateInit.rootCall=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ entry target childResult,
      RootBoundary input entry ∧ LocalEffects.erase entry=LocalEffects.erase source ∧
      OriginalCode.Installed entry.code ∧ OriginalScalarGlobals.Scalars entry.globals ∧
      entry.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      Rlp.Validation.Arena entry 2713714688#64 2701135872#64 ∧ Keccak256.Environment entry 2713714976#64 2713715176#64 ∧
      entry.clock=source.clock-1 ∧ evaluateHOLFiniteState entry Mpt.WitnessDecodeRoot.body=(childResult,target) ∧
      Mpt.StateInit.RootResumes source target post childResult outcome := by
  have callerBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,codeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩ := boundary
  rcases Mpt.StateInit.root_call_trace source post nodes root installed nodeCell rootCell outcome run with stopped|observed
  · exact Or.inl stopped
  · obtain ⟨entry,target,childResult,pure,clock,dbEntry,rootEntry,childRun,resumes⟩ := observed
    have data:=RootBoundary.of_state_init input source entry callerBoundary pure (dbEntry.trans nodeCell.symm)
    have frame:=runtime_of_entry source entry pure
    have entryInstalled : OriginalCode.Installed entry.code := by rw [frame.code]; exact installed
    have globals:=congrArg PanSemStateFiniteExact.globals pure
    change entry.globals=source.globals at globals
    have entryScalars : OriginalScalarGlobals.Scalars entry.globals := by rw [globals]; exact scalars
    exact Or.inr ⟨entry,target,childResult,data,pure,entryInstalled,entryScalars,rootEntry,
      frame.scratch source entry _ _ scratch,frame.hash_environment source entry _ _ environment,clock,childRun,resumes⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.root_entry_of_ready
