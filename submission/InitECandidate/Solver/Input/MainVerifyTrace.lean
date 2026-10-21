import InitECandidate.Solver.Input.MainVerifyProgram
import InitECandidate.Solver.Input.MainRequestRootHashTrace
import InitECandidate.Solver.Input.ScopedCallObserve
import InitECandidate.Solver.Input.VerifyTrace

namespace InitECandidate.Solver.Input.Main.Verification
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Main either stops at verification's return or runs its actual final
serialization/output continuation after a genuine scalar return. -/
def Resumes (source target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (childResult result : Option (PanSemResultExact 64)) : Prop :=
  post.clock=target.clock ∨ ∃ returned inner,
    childResult=some (.returned returned) ∧
    (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one)=true ∧
    evaluateHOLFiniteState (CallNormal.continuationEntry source target "succ" returned) afterVerify=(result,inner) ∧
    post=QueryBranch.restore source "succ" inner

/-- The genuine post-hash state supplies main's SI argument and installed
original823. Every funded scoped call exposes its actual verify execution,
without assuming the callee or the rest of main returns normally. -/
theorem trace (input : Guest.InputBlob) (caller origin hashed post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (actual : DecoderCall.DecoderReady input caller origin) (returned : RequestHash.Returned input origin hashed root)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState hashed RequestHash.continuation=(result,post)) :
    hashed.clock-post.clock≤1 ∨ ∃ entry target childResult,
      1≤hashed.clock ∧ LocalEffects.erase entry=LocalEffects.erase hashed ∧ entry.clock=hashed.clock-1 ∧
      entry.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))) ∧
      evaluateHOLFiniteState entry Verify.body=(childResult,target) ∧ Resumes hashed target post childResult result := by
  have si : hashed.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))) :=
    (returned.locals _).trans (RequestHash.entered_fields input caller origin root actual).2.1
  have args : evalListHOLFinite hashed (h:=fun address=>Classical.propDecidable (hashed.memaddrs address)) arguments=
      some [.val (.word (RequestPrefix.cursor input))] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,QueryBranch.localVar,toExact,si]
  obtain ⟨callee,called,siCell⟩ := word_environment hashed.code.lookup (ofString "verify_stateless_new_payload") (ofString "si") Verify.body .one
    (RequestPrefix.cursor input) (Verify.original_code hashed.code returned.workspace.sha.installed)
  rw [original_shape] at run
  rcases CallNormal.scoped_observe hashed post "succ" .one (ofString "verify_stateless_new_payload") arguments _ Verify.body afterVerify callee .one args called result run with stopped|observed
  · exact Or.inl stopped
  · obtain ⟨childResult,target,funded,childRun,remaining⟩ := observed
    exact Or.inr ⟨callEntryStateHOLFinite hashed callee,target,childResult,funded,rfl,rfl,siCell,childRun,remaining⟩

end InitECandidate.Solver.Input.Main.Verification

#print axioms InitECandidate.Solver.Input.Main.Verification.trace
