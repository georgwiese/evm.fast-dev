import InitECandidate.Solver.Input.BytesList.Loop

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual initialized check loop, pair return and index-scope restoration.
It reads no record at count zero, so array zero is included. -/
theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array maximum : BitVec 64) (count : Nat)
    (lengths : Nat→BitVec 64) (small : count<2^63)
    (r : source.locals.lookup (ofString "r")=some (pairValue array count))
    (m : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (mapped : ∀ position<count,source.memaddrs (cell array position))
    (stored : ∀ position<count,source.memory (cell array position)=.word (lengths position))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : count+1≤source.clock) :
    ∃ result target paid,evaluateHOLFiniteState source tail=(result,target) ∧ paid≤count+1 ∧
      target.clock=source.clock-paid ∧ frame target=frame source ∧ target.memory=source.memory ∧
      ((result=some (.returned (pairValue array count)) ∧ paid=count ∧
        ∀ position<count,(lengths position).toNat≤maximum.toNat) ∨
       result=some (.exception (ofString "SszErr") (.val (.word 70#64)))) := by
  classical
  let entry:=bind source "i" 0#64
  have i : entry.locals.lookup (ofString "i")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have r' : entry.locals.lookup (ofString "r")=some (pairValue array count):=(bind_lookup_other source "i" "r" _ (by decide)).trans r
  have m' : entry.locals.lookup (ofString "maxb")=some (.val (.word maximum)):=(bind_lookup_other source "i" "maxb" _ (by decide)).trans m
  obtain ⟨result,loopPost,paid,loopRun,bound,clock,frames,memory,outcome⟩:=loop_execute entry array maximum lengths 0 count count (by omega) small i r' m' mapped stored failCode exceptionShape enough
  rcases outcome with normal|fault
  · have returnRun : evaluateHOLFiniteState loopPost returnArray=(some (.returned (pairValue array count)),emptyLocalsHOLFinite loopPost) := by
      simp [returnArray,evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,normal.2.2.1,pairValue,VarList.pairValue,
        shapeOfHOLExact,sizeOfShapeWithContextHOL]
    have initializedRun : evaluateHOLFiniteState entry initializedTail=(some (.returned (pairValue array count)),emptyLocalsHOLFinite loopPost) := by
      rw [initializedTail,WitnessRadix.StateSteps.next_sequence entry loopPost _ _ (by simpa only [normal.1] using loopRun) (by rw [clock]; omega)]
      exact returnRun
    have actual:=ScalarScope.declare_execute source (emptyLocalsHOLFinite loopPost) "i" (.const 0#64) 0#64 initializedTail
      (some (.returned (pairValue array count))) rfl initializedRun
    refine ⟨_,restore source "i" (emptyLocalsHOLFinite loopPost),paid,actual,bound,clock,frames,memory,Or.inl ⟨rfl,normal.2.1,?_⟩⟩
    intro position inside
    exact normal.2.2.2 position (by omega) inside
  · have failed : evaluateHOLFiniteState entry initializedTail=(some (.exception (ofString "SszErr") (.val (.word 70#64))),loopPost) := by
      exact WitnessRadix.StateSteps.stopped_sequence entry loopPost loop returnArray (.exception (ofString "SszErr") (.val (.word 70#64)))
        (by simpa only [fault] using loopRun) (by rw [clock]; omega)
    have actual:=ScalarScope.declare_execute source loopPost "i" (.const 0#64) 0#64 initializedTail
      (some (.exception (ofString "SszErr") (.val (.word 70#64)))) rfl failed
    exact ⟨_,restore source "i" loopPost,paid,actual,bound,clock,frames,memory,Or.inr rfl⟩

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.tail_execute
