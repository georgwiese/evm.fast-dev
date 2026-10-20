import InitECandidate.Solver.Input.UDivMod.Call
import InitECandidate.Solver.Input.TerminatingPaddedScopeArgs

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Execute the actual original unsigned divider under any non-timeout
scoped call. Its real caller and zero-or64 loop ticks are funded by that run;
the continuation may return, raise, fail or terminate through FFI. -/
theorem call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (nonzero : b ≠ 0#64) (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some (values a b))
    (code : source.code.lookup (ofString "udivmod") = some (formals,body,returnShape))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "udivmod") expressions continuation) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ next innerPost q r paid,paid ≤ 65 ∧ paid ≤ source.clock ∧
      next.locals = source.locals.update (ofString name,pairValue q r) ∧ next.clock = source.clock - paid ∧
      frozen next = frozen source ∧ (b.toNat ≤ 2^63 → q.toNat = a.toNat / b.toNat ∧ r.toNat = a.toNat % b.toNat) ∧
      evaluateHOLFiniteState next continuation = (result,innerPost) ∧ post = restore source name innerPost := by
  obtain ⟨callee,called,aLocal,bLocal⟩ := environment source.code.lookup a b code
  let padded := callEntryStateHOLFinite {source with clock := source.clock + 65} callee
  obtain ⟨middle,q,r,paid,bound,bodyRun,clock,frame,arithmetic⟩ := body_execute_nonzero padded a b aLocal bLocal nonzero (by change 64 ≤ source.clock + 65 - 1; omega)
  have shapePass : (shapeEqHOL (shapeOfHOLExact (pairValue q r)) returnShape && shapeEqHOL (shapeOfHOLExact (pairValue q r)) returnShape) = true := by
    simp [pairValue,returnShape,shapeOfHOLExact,shapeEqHOL_eq_true]
  obtain ⟨funded,positive,lowered,innerPost,remaining,restored⟩ := terminating_padded_scope_args source post middle name returnShape (ofString "udivmod") expressions (values a b)
    body continuation callee returnShape (pairValue q r) 65 args called (by decide) bodyRun shapePass result run notTimeout
  let next := CallNormal.continuationEntry source {middle with clock := middle.clock - 65} name (pairValue q r)
  have clockEq : middle.clock = source.clock + 65 - 1 - paid := clock
  have actualPaid : paid + 1 ≤ source.clock := by omega
  have nextClock : next.clock = source.clock - (paid + 1) := by change middle.clock - 65 = _; omega
  exact ⟨next,innerPost,q,r,paid+1,by omega,actualPaid,rfl,nextClock,frame,arithmetic,remaining,restored⟩

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.call_trace
