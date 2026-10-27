import InitECandidate.Solver.Input.FixedList.Environment
import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.Input.NormalCallClock
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.FixedList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual normal data and cost of fixed-list counting, at the original clock.
Clock extension funds the known division proof, without assuming future time. -/
theorem normal_any_clock (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length size limit : BitVec 64)
    (n : source.locals.lookup (ofString "len") = some (.val (.word length)))
    (s : source.locals.lookup (ofString "sz") = some (.val (.word size)))
    (l : source.locals.lookup (ofString "lim") = some (.val (.word limit))) (nonzero : size ≠ 0#64)
    (divisionCode : source.code.lookup (ofString "udivmod") = some (UDivMod.formals, UDivMod.body, UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals, SszFail.body, .one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ count, value = .val (.word count) ∧ count.toNat ≤ limit.toNat ∧
      UDivMod.frozen post = UDivMod.frozen source ∧ source.clock - post.clock ≤ 65 ∧ post.clock ≤ source.clock ∧
      (size.toNat ≤ 2^63 → count.toNat = length.toNat / size.toNat ∧ length.toNat % size.toNat = 0) := by
  have padded := panPropsEvaluateAddClockEq body source (some (.returned value)) post 66 ⟨run, by intro impossible; cases impossible⟩
  obtain ⟨count, paid, bound, returned, countBound, clock, frame, arithmetic⟩ :=
    normal_summary {source with clock := source.clock + 66} {post with clock := post.clock + 66}
      length size limit n s l nonzero divisionCode failCode exceptionShape (by change 66 ≤ source.clock + 66; omega) value padded
  change post.clock + 66 = source.clock + 66 - paid at clock
  exact ⟨count, returned, countBound, frame, by omega, by omega, arithmetic⟩

/-- Actual fixed-list caller resumption, with no minimum clock premise. The
real returned count, saved locals, unchanged memory/control and cost are retained. -/
theorem caller_any_clock (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length size limit : BitVec 64)
    (nonzero : size ≠ 0#64)
    (divisionCode : source.code.lookup (ofString "udivmod") = some (UDivMod.formals, UDivMod.body, UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals, SszFail.body, .one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (code : source.code.lookup (ofString "ssz_fixed_list_count") = some (formals, body, .one))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some (values length size limit))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "ssz_fixed_list_count") expressions continuation) = (some (.returned value), post)) :
    ∃ next innerPost count, next.locals = source.locals.update (ofString name, .val (.word count)) ∧
      count.toNat ≤ limit.toNat ∧ UDivMod.frozen next = UDivMod.frozen source ∧
      source.clock - next.clock ≤ 66 ∧ next.clock ≤ source.clock ∧
      evaluateHOLFiniteState next continuation = (some (.returned value), innerPost) ∧ post = restore source name innerPost ∧
      (size.toNat ≤ 2^63 → count.toNat = length.toNat / size.toNat ∧ length.toNat % size.toNat = 0) := by
  classical
  obtain ⟨callee, called, n, s, l⟩ := environment source.code.lookup length size limit code
  have positive := CallNormal.normal_clock source post (ofString name) .one (ofString "ssz_fixed_list_count") expressions continuation value run
  obtain ⟨bodyPost, returned, bodyRun⟩ := CallNormal.callee_return source post (ofString name) .one (ofString "ssz_fixed_list_count") expressions
    (values length size limit) body continuation callee .one args called positive value run
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨count, valueEq, countBound, frame, price, clock, arithmetic⟩ := normal_any_clock entry bodyPost length size limit n s l nonzero
    divisionCode failCode exceptionShape returned bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one) = true := by
    rw [valueEq]
    simp [shapeOfHOLExact, shapeEqHOL]
  have invoked := CallNormal.return_execute source bodyPost name .one (ofString "ssz_fixed_list_count") expressions (values length size limit)
    body continuation callee .one returned args called positive bodyRun shapePass
  have actual := invoked.symm.trans run
  let next := CallNormal.continuationEntry source bodyPost name returned
  have resumed : (evaluateHOLFiniteState next continuation).1 = some (.returned value) := congrArg Prod.fst actual
  refine ⟨next, (evaluateHOLFiniteState next continuation).2, count, ?_, countBound, ?_, ?_, ?_, Prod.ext resumed rfl,
    (congrArg Prod.snd actual).symm, arithmetic⟩
  · change source.locals.update (ofString name, returned) = source.locals.update (ofString name, .val (.word count))
    rw [valueEq]
  · change UDivMod.frozen bodyPost = UDivMod.frozen source
    exact frame
  · change source.clock - bodyPost.clock ≤ 66
    change source.clock - 1 - bodyPost.clock ≤ 65 at price
    omega
  · change bodyPost.clock ≤ source.clock
    change bodyPost.clock ≤ source.clock - 1 at clock
    omega

end InitECandidate.Solver.Input.FixedList

#print axioms InitECandidate.Solver.Input.FixedList.normal_any_clock
#print axioms InitECandidate.Solver.Input.FixedList.caller_any_clock
