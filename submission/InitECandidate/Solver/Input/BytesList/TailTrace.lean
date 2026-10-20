import InitECandidate.Solver.Input.BytesList.Tail
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The observed original byte-size loop and return, at any actual clock.
A rejection costs its real loop iterations plus its SszErr70 call. -/
theorem tail_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array maximum : BitVec 64) (count : Nat)
    (lengths : Nat→BitVec 64) (small : count<2^63)
    (r : source.locals.lookup (ofString "r")=some (pairValue array count))
    (m : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (mapped : ∀ position<count,source.memaddrs (cell array position))
    (stored : ∀ position<count,source.memory (cell array position)=.word (lengths position))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source tail=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤count+1 ∧ frame post=frame source ∧ post.memory=source.memory ∧
      ((result=some (.returned (pairValue array count)) ∧ ∀ position<count,(lengths position).toNat≤maximum.toNat) ∨
       result=some (.exception (ofString "SszErr") (.val (.word 70#64)))) := by
  let padding := count+1
  have paddedRun := panPropsEvaluateAddClockEq tail source result post padding ⟨run,notTimeout⟩
  obtain ⟨computedResult,target,paid,computed,bound,clock,frames,memory,outcome⟩ := tail_execute {source with clock:=source.clock+padding}
    array maximum count lengths small r m mapped stored failCode exceptionShape (by change count+1≤source.clock+padding; dsimp only [padding]; omega)
  have equality := computed.symm.trans paddedRun
  have answer : computedResult=result := congrArg Prod.fst equality
  have endpoint : target={post with clock:=post.clock+padding} := congrArg Prod.snd equality
  rw [endpoint] at clock frames memory
  change post.clock+padding=source.clock+padding-paid at clock
  have actualFrame : frame post=frame source := frames
  refine ⟨by dsimp only [padding] at clock; omega,actualFrame,memory,?_⟩
  rcases outcome with normal | fault
  · exact Or.inl ⟨answer.symm.trans normal.1,normal.2.2⟩
  · exact Or.inr (answer.symm.trans fault)

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.tail_trace
