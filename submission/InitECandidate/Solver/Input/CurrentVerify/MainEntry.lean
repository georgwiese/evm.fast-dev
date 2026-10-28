import InitECandidate.Solver.Input.CurrentHash.HashPrefix
import InitECandidate.Solver.Input.VerifyTrace
import InitECandidate.Solver.Input.ScopedCallObserve

namespace InitECandidate.Solver.Input.CurrentVerify.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def arguments : List (ExpHOL 64) := [localVar "si"]
def afterVerify : ProgHOL 64 := match CurrentHash.HashPrefix.afterHash with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem source_shape : CurrentHash.HashPrefix.afterHash=
    .decCall (ofString "succ") .one (ofString "verify_stateless_new_payload") arguments afterVerify := by
  simp only [CurrentHash.HashPrefix.afterHash,CurrentHash.HashPrefix.decoderTail,
    CurrentStartup.DecoderPrefix.afterDecoder,CurrentStartup.afterStartup,
    Input.Main.afterMemory,Input.Main.body,CallPrefix.cutAt,CurrentStartup.seqTail,
    Guest.Software.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,arguments,afterVerify,localVar]

/-- The actual final serialization/output continuation is kept separate from
the callee's cost, on normal returns and every earlier stopped outcome. -/
def Resumes (source target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (childResult result : Option (PanSemResultExact 64)) : Prop :=
  post.clock=target.clock ∨ ∃ returned inner,
    childResult=some (.returned returned) ∧
    (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one)=true ∧
    evaluateHOLFiniteState (CallNormal.continuationEntry source target "succ" returned) afterVerify=(result,inner) ∧
    post=restore source "succ" inner

/-- The current post-hash main continuation selects its genuine verify body,
then the checked eight-wrapper prefix. Actual caller bindings and installed
code suffice; no successful future verification is assumed. -/
theorem trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (si : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source CurrentHash.HashPrefix.afterHash=(result,post)) :
    source.clock-post.clock≤1 ∨ ∃ entry target childResult,
      1≤source.clock ∧ LocalEffects.erase entry=LocalEffects.erase source ∧ entry.clock=source.clock-1 ∧
      entry.locals.lookup (ofString "si")=some (.val (.word si)) ∧
      evaluateHOLFiniteState entry Verify.body=(childResult,target) ∧
      (entry.clock-target.clock≤8 ∨ AttemptWrapper.Reaches entry target si 8) ∧ Resumes source target post childResult result := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word si)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,siLocal]
  obtain ⟨callee,called,siCell⟩ := word_environment source.code.lookup (ofString "verify_stateless_new_payload") (ofString "si") Verify.body .one si (Verify.original_code source.code installed)
  rw [source_shape] at actual
  rcases CallNormal.scoped_observe source post "succ" .one (ofString "verify_stateless_new_payload") arguments _ Verify.body afterVerify callee .one args called result actual with stopped|observed
  · exact Or.inl stopped
  · obtain ⟨childResult,target,funded,childRun,remaining⟩ := observed
    have wrappers:=Verify.to_run (callEntryStateHOLFinite source callee) target si installed siCell childResult childRun
    exact Or.inr ⟨callEntryStateHOLFinite source callee,target,childResult,funded,rfl,rfl,siCell,childRun,wrappers,remaining⟩

end InitECandidate.Solver.Input.CurrentVerify.Main

#print axioms InitECandidate.Solver.Input.CurrentVerify.Main.source_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.Main.trace
