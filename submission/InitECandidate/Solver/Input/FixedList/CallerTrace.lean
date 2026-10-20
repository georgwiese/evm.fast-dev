import InitECandidate.Solver.Input.FixedList.Trace
import InitECandidate.Solver.Input.FixedList.Environment
import InitECandidate.Solver.Input.NonTimeoutScopedCall

namespace InitECandidate.Solver.Input.FixedList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real fixed-list call either raises its actual parser error within67
source ticks, or resumes the unchanged continuation with its derived count
and exact unchanged memory/globals/FFI fields. No callee success is assumed. -/
theorem caller_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length size limit : BitVec 64)
    (nonzero : size ≠ 0#64)
    (divisionCode : source.code.lookup (ofString "udivmod") = some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (code : source.code.lookup (ofString "ssz_fixed_list_count") = some (formals,body,.one))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some (values length size limit))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "ssz_fixed_list_count") expressions continuation) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 30#64 ∨ error = 31#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 67) ∨
    (∃ next innerPost count,next.locals = source.locals.update (ofString name,.val (.word count)) ∧ count.toNat ≤ limit.toNat ∧
      next.clock ≤ source.clock ∧ source.clock - next.clock ≤ 67 ∧ UDivMod.frozen next = UDivMod.frozen source ∧
      evaluateHOLFiniteState next continuation = (result,innerPost) ∧ post = restore source name innerPost ∧
      (size.toNat ≤ 2^63 → count.toNat = length.toNat / size.toNat ∧ length.toNat % size.toNat = 0)) := by
  obtain ⟨callee,called,n,s,l⟩ := environment source.code.lookup length size limit code
  obtain ⟨funded,bodyNonTimeout⟩ := scoped_call_non_timeout source post (ofString name) .one (ofString "ssz_fixed_list_count") expressions
    (values length size limit) body continuation callee .one args called result run notTimeout
  let entry := callEntryStateHOLFinite source callee
  let bodyResult := (evaluateHOLFiniteState entry body).1
  let bodyPost := (evaluateHOLFiniteState entry body).2
  have bodyRun : evaluateHOLFiniteState entry body = (bodyResult,bodyPost) := rfl
  obtain ⟨cost,outcome⟩ := body_trace entry bodyPost length size limit n s l nonzero divisionCode failCode exceptionShape bodyResult bodyRun bodyNonTimeout
  have forward : bodyPost.clock ≤ source.clock - 1 := evaluateHOLFiniteState_clock_le entry body
  have callerCost : source.clock - bodyPost.clock ≤ 67 := by change source.clock - 1 - bodyPost.clock ≤ 66 at cost; omega
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    have actualBody : evaluateHOLFiniteState entry body = (some (.exception (ofString "SszErr") (.val (.word error))),bodyPost) := Prod.ext same rfl
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
    simp only [args,called,if_neg (show source.clock ≠ 0 by omega)] at run
    rw [actualBody] at run
    have endpoint : post.clock = bodyPost.clock := by
      have projected := congrArg (fun output => output.2.clock) run
      exact projected.symm
    exact Or.inl ⟨error,allowed,(congrArg Prod.fst run).symm,by rw [endpoint]; exact callerCost⟩
  · obtain ⟨count,same,countBound,frame,arithmetic⟩ := normal
    have actualBody : evaluateHOLFiniteState entry body = (some (.returned (.val (.word count))),bodyPost) := Prod.ext same rfl
    have shapePass : (shapeEqHOL (shapeOfHOLExact (.val (.word count))) .one && shapeEqHOL (shapeOfHOLExact (.val (.word count))) .one) = true := by simp [shapeOfHOLExact,shapeEqHOL]
    have actual := CallNormal.return_execute source bodyPost name .one (ofString "ssz_fixed_list_count") expressions (values length size limit)
      body continuation callee .one (.val (.word count)) args called funded actualBody shapePass
    have remaining := actual.symm.trans run
    let next := CallNormal.continuationEntry source bodyPost name (.val (.word count))
    let innerPost := (evaluateHOLFiniteState next continuation).2
    have observed := congrArg Prod.fst remaining
    have endpoint : post = restore source name innerPost := (congrArg Prod.snd remaining).symm
    exact Or.inr ⟨next,innerPost,count,rfl,countBound,by change bodyPost.clock ≤ source.clock; omega,callerCost,frame,Prod.ext observed rfl,endpoint,arithmetic⟩

end InitECandidate.Solver.Input.FixedList

#print axioms InitECandidate.Solver.Input.FixedList.caller_trace
