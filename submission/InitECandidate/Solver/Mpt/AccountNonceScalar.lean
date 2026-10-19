import InitECandidate.Solver.Mpt.AccountDecodeLoops
import InitECandidate.Solver.Input.LoopInvariant
import InitECandidate.Solver.Input.NoneControl
import InitECandidate.Solver.Input.ScalarAssignNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine normal nonce loop retains a scalar accumulator from its real
initial scalar declaration. Successful byte-expression evaluation is derived
at each actual assignment, not assumed as a future-read oracle. -/
theorem nonce_loop_scalar (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (cell : source.locals.lookup (ofString "nonce")=some (.val (.word word)))
    (normal : evaluateHOLFiniteState source nonceLoop=(none,post)) :
    ∃ next : BitVec 64,post.locals.lookup (ofString "nonce")=some (.val (.word next)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    ∃ value : BitVec 64,current.locals.lookup (ofString "nonce")=some (.val (.word value))
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ observed,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) (.cmp .lower (localVar "i") (field "f0" 2))=some (.val (.word observed)) →
      observed≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) nonceLoopBody=(none,target) → invariant target := by
    intro current codeEq valid observed read nonzero clock target bodyRun
    obtain ⟨old,oldCell⟩ := valid
    rw [nonce_body_shape] at bodyRun
    obtain ⟨middle,accumulated,incremented⟩ := Input.sequence_none (decClockHOLFinite current) target nonceAccumulate increment bodyRun
    obtain ⟨next,expressionRead,middleEq⟩ := Input.scalar_assign_none (decClockHOLFinite current) middle "nonce" _ old oldCell accumulated
    have middleCell : middle.locals.lookup (ofString "nonce")=some (.val (.word next)) := by rw [middleEq]; exact bind_lookup_same _ _ _
    have safe : Input.LocalPrefix (ofString "nonce") increment := .assign _ _ (by decide)
    have summary := safe.summary_full middle
    unfold Input.LocalSummary at summary
    rw [incremented] at summary
    exact ⟨next,(summary.1 rfl).trans middleCell⟩
  rw [nonce_loop_shape] at normal
  exact Input.loop_invariant source.code (ofString "f0") (.cmp .lower (localVar "i") (field "f0" 2)) nonceLoopBody nonce_body_safe invariant step
    source post rfl ⟨word,cell⟩ normal

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_loop_scalar
