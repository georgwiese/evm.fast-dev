import InitECandidate.Solver.Input.UDivMod.CallTrace
import InitECandidate.Solver.Input.FixedList.Normal
import InitECandidate.Solver.Input.SszGuardTrace

namespace InitECandidate.Solver.Input.FixedList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both original fixed-list guards at the actual clock. Rejections raise
SszErr30/31 and spend one call tick; passing returns the real quotient. -/
theorem tail_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (q r limit : BitVec 64)
    (qr : source.locals.lookup (ofString "qr") = some (UDivMod.pairValue q r))
    (lim : source.locals.lookup (ofString "lim") = some (.val (.word limit)))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source tail = (result,post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 1 ∧
      ((∃ error : BitVec 64,(error = 30#64 ∨ error = 31#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error)))) ∨
        (r = 0#64 ∧ q.toNat ≤ limit.toNat ∧ result = some (.returned (.val (.word q))) ∧ post = emptyLocalsHOLFinite source)) := by
  classical
  have remTest : eval source remainderTest = some (.val (.word (if r ≠ 0#64 then 1#64 else 0#64))) := by
    by_cases zero : r = 0#64 <;>
      simp [eval,remainderTest,remainder,localVar,UDivMod.pairValue,evalHOLExact,toExact,qr,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
  have limTest : eval source limitTest = some (.val (.word (if limit.toNat < q.toNat then 1#64 else 0#64))) := by
    simp [eval,limitTest,quotient,localVar,UDivMod.pairValue,evalHOLExact,toExact,qr,lim,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  rcases Header.guard_trace source post remainderTest 30#64 (r ≠ 0#64) limitTail remTest failCode exceptionShape result run notTimeout with rejected | passed
  · obtain ⟨bad,funded,same,endpoint⟩ := rejected
    exact ⟨by rw [endpoint]; change source.clock - (source.clock - 1) ≤ 1; omega,Or.inl ⟨30#64,Or.inl rfl,same⟩⟩
  · obtain ⟨zero,remaining⟩ := passed
    rcases Header.guard_trace source post limitTest 31#64 (limit.toNat < q.toNat) returnCount limTest failCode exceptionShape result remaining notTimeout with rejected | passed
    · obtain ⟨bad,funded,same,endpoint⟩ := rejected
      exact ⟨by rw [endpoint]; change source.clock - (source.clock - 1) ≤ 1; omega,Or.inl ⟨31#64,Or.inr rfl,same⟩⟩
    · obtain ⟨bound,returned⟩ := passed
      have actual : evaluateHOLFiniteState source returnCount = (some (.returned (.val (.word q))),emptyLocalsHOLFinite source) := by
        simp [returnCount,quotient,localVar,UDivMod.pairValue,evaluateHOLFiniteState_return,evalHOLExact,toExact,qr,shapeOfHOLExact,sizeOfShapeWithContextHOL]
      have same := actual.symm.trans returned
      have endpoint : post = emptyLocalsHOLFinite source := (congrArg Prod.snd same).symm
      exact ⟨by rw [endpoint]; change source.clock - source.clock ≤ 1; omega,
        Or.inr ⟨by simpa using zero,by omega,(congrArg Prod.fst same).symm,endpoint⟩⟩

/-- Complete original fixed-list body on every non-timeout result. No clock
allowance or normal helper outcome is assumed. Its actual cost is at most66;
the only rejections are the original SszErr30/31. -/
theorem body_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length size limit : BitVec 64)
    (n : source.locals.lookup (ofString "len") = some (.val (.word length)))
    (s : source.locals.lookup (ofString "sz") = some (.val (.word size)))
    (l : source.locals.lookup (ofString "lim") = some (.val (.word limit))) (nonzero : size ≠ 0#64)
    (divisionCode : source.code.lookup (ofString "udivmod") = some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body = (result,post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 66 ∧
      ((∃ error : BitVec 64,(error = 30#64 ∨ error = 31#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error)))) ∨
        (∃ count : BitVec 64,result = some (.returned (.val (.word count))) ∧ count.toNat ≤ limit.toNat ∧
          UDivMod.frozen post = UDivMod.frozen source ∧ (size.toNat ≤ 2^63 → count.toNat = length.toNat / size.toNat ∧ length.toNat % size.toNat = 0))) := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (UDivMod.values length size) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,arguments,UDivMod.values,localVar,n,s]
  rw [body_shape] at run
  obtain ⟨next,innerPost,q,r,paid,bound,funded,localsEq,clock,frame,arithmetic,remaining,restored⟩ := UDivMod.call_trace source post length size nonzero "qr" arguments tail args divisionCode result run notTimeout
  have qr : next.locals.lookup (ofString "qr") = some (UDivMod.pairValue q r) := by
    rw [localsEq]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have lim : next.locals.lookup (ofString "lim") = some (.val (.word limit)) := by
    rw [localsEq]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "qr" == ofString "lim") = false from by decide] using l
  have codeEq : next.code = source.code := by
    have projected := congrArg PanSemStateFiniteExact.code frame
    exact projected
  have shapesEq : next.eshapes = source.eshapes := by
    have projected := congrArg PanSemStateFiniteExact.eshapes frame
    exact projected
  obtain ⟨tailCost,outcome⟩ := tail_trace next innerPost q r limit qr lim (by rw [codeEq]; exact failCode) (by rw [shapesEq]; exact exceptionShape) result remaining notTimeout
  have endpoint : post.clock = innerPost.clock := by rw [restored]; rfl
  have forward := evaluateHOLFiniteState_clock_le next tail
  rw [remaining] at forward
  change innerPost.clock ≤ next.clock at forward
  refine ⟨by rw [endpoint]; omega,?_⟩
  rcases outcome with rejected | normal
  · exact Or.inl rejected
  · obtain ⟨zero,countBound,same,innerEq⟩ := normal
    refine Or.inr ⟨q,same,countBound,?_,?_⟩
    · rw [restored,innerEq]
      exact frame
    · intro small
      obtain ⟨quotient,remainder⟩ := arithmetic small
      exact ⟨quotient,by rw [zero] at remainder; exact remainder.symm⟩

end InitECandidate.Solver.Input.FixedList

#print axioms InitECandidate.Solver.Input.FixedList.tail_trace
#print axioms InitECandidate.Solver.Input.FixedList.body_trace
