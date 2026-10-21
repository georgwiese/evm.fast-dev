import InitECandidate.Solver.Input.RootLookupOfEntry
import InitECandidate.Solver.Input.RootLookupCallTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessConstructors

/-- The actual original root body reaches its decode/failure suffix with
the real bounded witness answer and all physical/runtime data intact, or
stops within the complete original comparison/lookup allowance. -/
theorem root_after_lookup_of_entry (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (boundary : RootBoundary input source) (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Mpt.WitnessDecodeRoot.body=(outcome,post)) :
    source.clock-post.clock≤6*nodeCount input+9 ∨ ∃ lookupSource nodes current answer inner,
      RootBoundary input current ∧ LocalEffects.erase current=LocalEffects.erase source ∧
      OriginalCode.Installed current.code ∧ OriginalScalarGlobals.Scalars current.globals ∧
      current.locals.lookup (ofString "db")=some (.val (.word nodes)) ∧ current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      current.locals.lookup (ofString "r")=some (MutableTable.NodeDb.output answer) ∧
      Rlp.Validation.Arena current 2713714688#64 2701135872#64 ∧ Keccak256.Environment current 2713714976#64 2713715176#64 ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤6*nodeCount input+9 ∧
      (∀ slice,answer=some slice→∃ index<nodeCount input,slice=nodeSlices input index ∧ slice.2.toNat≤1024 ∧
        AllocatedBytes.Arena slice.1 slice.2.toNat ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤nodes.toNat) ∧
      evaluateHOLFiniteState current Mpt.WitnessDecodeRoot.afterLookup=(outcome,inner) ∧
      post=QueryBranch.restore source "is_empty" (QueryBranch.restore lookupSource "r" inner) := by
  rcases root_lookup_of_entry input source post root boundary installed scalars rootCell scratch environment outcome run with stopped|lookup
  · exact Or.inl (by omega)
  · obtain ⟨lookupSource,lookupPost,lookupBoundary,lookupPure,lookupInstalled,lookupScalars,lookupRoot,lookupScratch,lookupEnvironment,forward,spent,lookupRun,endpoint⟩ := lookup
    have endpointClock : post.clock=lookupPost.clock := (congrArg PanSemStateFiniteExact.clock endpoint).trans (QueryBranch.restore_clock source lookupPost "is_empty")
    rcases root_lookup_call_trace input lookupSource lookupPost root lookupBoundary lookupInstalled lookupRoot outcome lookupRun with stopped|reached
    · have back:=evaluateHOLFiniteState_clock_le lookupSource Mpt.WitnessDecodeRoot.lookupCall
      rw [lookupRun] at back
      exact Or.inl (by omega)
    · obtain ⟨nodes,current,answer,inner,data,pure,dbCurrent,rootCurrent,rCurrent,currentForward,currentSpent,hit,continued,lookupEnd⟩ := reached
      have wholePure:=pure.trans lookupPure
      have frame:=runtime_of_entry source current wholePure
      have currentInstalled : OriginalCode.Installed current.code := by rw [frame.code]; exact installed
      have globals:=congrArg PanSemStateFiniteExact.globals wholePure
      change current.globals=source.globals at globals
      have currentScalars : OriginalScalarGlobals.Scalars current.globals := by rw [globals]; exact scalars
      have finalEndpoint:=endpoint.trans (congrArg (QueryBranch.restore source "is_empty") lookupEnd)
      exact Or.inr ⟨lookupSource,nodes,current,answer,inner,data,wholePure,currentInstalled,currentScalars,dbCurrent,rootCurrent,rCurrent,
        frame.scratch source current _ _ scratch,frame.hash_environment source current _ _ environment,by omega,by omega,hit,continued,finalEndpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.root_after_lookup_of_entry
