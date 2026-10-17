import InitECandidate.Solver.Input.BytesList.Step
import InitECandidate.Solver.Input.WhileActive

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The entire actual read-only size-check loop, on arbitrary record lengths.
It establishes every bound or raises the real SszErr70, with no memory writes. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array maximum : BitVec 64) (lengths : Nat→BitVec 64)
    (index rounds count : Nat) (finish : index+rounds=count) (small : count<2^63)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (r : source.locals.lookup (ofString "r")=some (pairValue array count))
    (m : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (mapped : ∀ position<count,source.memaddrs (cell array position))
    (stored : ∀ position<count,source.memory (cell array position)=.word (lengths position))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : rounds+1≤source.clock) :
    ∃ result target paid,evaluateHOLFiniteState source loop=(result,target) ∧ paid≤rounds+1 ∧
      target.clock=source.clock-paid ∧ frame target=frame source ∧ target.memory=source.memory ∧
      ((result=none ∧ paid=rounds ∧ target.locals.lookup (ofString "r")=some (pairValue array count) ∧
        ∀ position,index≤position→position<count→(lengths position).toNat≤maximum.toNat) ∨
       result=some (.exception (ofString "SszErr") (.val (.word 70#64)))) := by
  classical
  induction rounds generalizing source index with
  | zero=>
    have inactive : ¬index<count := by omega
    have test:=loop_test source array index count (by omega) small i r
    simp only [if_neg inactive] at test
    have bridge : evalHOLFinite source loopTest=eval source loopTest :=
      congrArg (fun h : DecidablePred source.memaddrs=>@evalHOLExact 64 Guest.HostMemory _ source.toExact h loopTest) (Subsingleton.elim _ _)
    have finiteTest:=bridge.trans test
    refine ⟨none,source,0,?_,by omega,by simp,rfl,rfl,Or.inl ⟨rfl,rfl,r,?_⟩⟩
    · rw [loop,evaluateHOLFiniteState_while_total,finiteTest]
      simp
    · intro position low high; omega
  | succ rounds ih=>
    have active : index<count := by omega
    have test:=loop_test source array index count (by omega) small i r
    simp only [if_pos active] at test
    let entry:=decClockHOLFinite source
    have bodyRun:=body_execute entry array maximum (lengths index) index count i r m (mapped index active) (stored index active) failCode exceptionShape
      (by change 1≤source.clock-1; omega)
    by_cases rejected : maximum.toNat<(lengths index).toNat
    · simp only [if_pos rejected] at bodyRun
      let target:=emptyLocalsHOLFinite {entry with clock:=entry.clock-1}
      have clock : target.clock=source.clock-2 := by change source.clock-1-1=source.clock-2; omega
      have run:=while_active source target loopTest loopBody _ test (by omega) bodyRun (by rw [clock]; omega)
      refine ⟨_,target,2,run,by omega,clock,rfl,rfl,Or.inr rfl⟩
    · simp only [if_neg rejected] at bodyRun
      let next:=bind entry "i" (BitVec.ofNat 64 (index+1))
      have nextI : next.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))):=bind_lookup_same _ _ _
      have nextR : next.locals.lookup (ofString "r")=some (pairValue array count):=(bind_lookup_other entry "i" "r" _ (by decide)).trans r
      have nextM : next.locals.lookup (ofString "maxb")=some (.val (.word maximum)):=(bind_lookup_other entry "i" "maxb" _ (by decide)).trans m
      obtain ⟨result,target,paid,tailRun,bound,clock,frames,memory,outcome⟩:=ih next (index+1) (by omega) nextI nextR nextM mapped stored failCode exceptionShape
        (by change rounds+1≤source.clock-1; omega)
      have nextClock : next.clock=source.clock-1:=rfl
      have run:=while_active source next loopTest loopBody none test (by omega) bodyRun (by rw [nextClock])
      have actual : evaluateHOLFiniteState source loop=(result,target):=run.trans tailRun
      refine ⟨result,target,paid+1,actual,by omega,?_,frames,memory,?_⟩
      · change target.clock=source.clock-(paid+1)
        rw [nextClock] at clock
        omega
      · rcases outcome with normal|fault
        · refine Or.inl ⟨normal.1,by omega,normal.2.2.1,?_⟩
          intro position low high
          by_cases atCurrent : position=index
          · subst position; omega
          · exact normal.2.2.2 position (by omega) high
        · exact Or.inr fault

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.loop_execute
