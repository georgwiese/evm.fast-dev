import InitECandidate.Solver.Input.RootAfterLookupOfEntry
import InitECandidate.Solver.Mpt.WitnessLookupGuardTrace
import InitECandidate.Solver.Mpt.WitnessMaterializeCallTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessConstructors

/-- The real original root decoder reaches the true materializer with a
constructor-derived input slice and complete runtime/ownership, or stops
within the comparison/lookup/guard/caller allowance. -/
theorem materialize_entry_of_root (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (boundary : RootBoundary input source) (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Mpt.WitnessDecodeRoot.body=(outcome,post)) :
    source.clock-post.clock≤6*nodeCount input+10 ∨ ∃ lookupSource caller nodes slice index entry target childResult inner,
      RootBoundary input entry ∧ LocalEffects.erase entry=LocalEffects.erase source ∧
      OriginalCode.Installed entry.code ∧ OriginalScalarGlobals.Scalars entry.globals ∧
      entry.locals.lookup (ofString "db")=some (.val (.word nodes)) ∧ entry.locals.lookup (ofString "p")=some (.val (.word slice.1)) ∧
      entry.locals.lookup (ofString "n")=some (.val (.word slice.2)) ∧
      index<nodeCount input ∧ slice=nodeSlices input index ∧ slice.2.toNat≤1024 ∧ AllocatedBytes.Arena slice.1 slice.2.toNat ∧
      2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤nodes.toNat ∧
      Rlp.Validation.Arena entry 2713714688#64 2701135872#64 ∧ Keccak256.Environment entry 2713714976#64 2713715176#64 ∧
      entry.clock≤source.clock ∧ source.clock-entry.clock≤6*nodeCount input+10 ∧
      evaluateHOLFiniteState entry Mpt.WitnessMaterialize.body=(childResult,target) ∧
      Mpt.WitnessDecodeRoot.MaterializeResumes caller target inner childResult outcome ∧
      caller.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      post=QueryBranch.restore source "is_empty" (QueryBranch.restore lookupSource "r" inner) := by
  rcases root_after_lookup_of_entry input source post root boundary installed scalars rootCell scratch environment outcome run with stopped|lookup
  · exact Or.inl (by omega)
  · obtain ⟨lookupSource,nodes,caller,answer,inner,callerData,callerPure,callerInstalled,callerScalars,callerDb,callerRoot,callerR,callerScratch,callerEnvironment,forward,spent,hit,continued,endpoint⟩ := lookup
    have endpointClock : post.clock=inner.clock := (congrArg PanSemStateFiniteExact.clock endpoint).trans
      ((QueryBranch.restore_clock source (QueryBranch.restore lookupSource "r" inner) "is_empty").trans (QueryBranch.restore_clock lookupSource inner "r"))
    have stoppedPrice (stopped : caller.clock-inner.clock≤1) : source.clock-post.clock≤6*nodeCount input+10 := by
      have back:=evaluateHOLFiniteState_clock_le caller Mpt.WitnessDecodeRoot.afterLookup
      rw [continued] at back
      omega
    rcases Mpt.WitnessDecodeRoot.lookup_guard_trace caller inner answer callerInstalled callerR outcome continued with stopped|present
    · exact Or.inl (stoppedPrice stopped)
    · obtain ⟨slice,answerEq,materializeRun⟩ := present
      obtain ⟨index,indexInside,sliceEq,size,arena,lower,before⟩ := hit slice answerEq
      have presentR : caller.locals.lookup (ofString "r")=some (MutableTable.NodeDb.output (some slice)) := by rw [← answerEq]; exact callerR
      rcases Mpt.WitnessDecodeRoot.materialize_call_trace caller inner nodes slice callerInstalled callerDb presentR outcome materializeRun with stopped|observed
      · exact Or.inl (stoppedPrice stopped)
      · obtain ⟨entry,target,childResult,pure,clock,dbEntry,pEntry,nEntry,childRun,resumes⟩ := observed
        have data:=RootBoundary.erase_frame input caller entry callerData pure (dbEntry.trans callerDb.symm)
        have wholePure:=pure.trans callerPure
        have frame:=runtime_of_entry source entry wholePure
        have entryInstalled : OriginalCode.Installed entry.code := by rw [frame.code]; exact installed
        have globals:=congrArg PanSemStateFiniteExact.globals wholePure
        change entry.globals=source.globals at globals
        have entryScalars : OriginalScalarGlobals.Scalars entry.globals := by rw [globals]; exact scalars
        exact Or.inr ⟨lookupSource,caller,nodes,slice,index,entry,target,childResult,inner,data,wholePure,entryInstalled,entryScalars,dbEntry,pEntry,nEntry,
          indexInside,sliceEq,size,arena,lower,before,frame.scratch source entry _ _ scratch,frame.hash_environment source entry _ _ environment,
          by omega,by omega,childRun,resumes,callerRoot,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.materialize_entry_of_root
