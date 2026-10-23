import InitECandidate.Solver.Mpt.KeyToNibblesPrefixedBlock
import InitECandidate.Solver.Mpt.KeyToNibblesAnyLoops

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual bounded converter loop retains the full nibble prefix,
including a preceding compact-path nibble. Funding is used only to build
an execution; the normal-return contract later removes that premise. -/
theorem prefixed_loop_execute (test : ExpHOL 64) (loopBody : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (key out : BitVec 64) (leading : Nat)
    (reads : Input.CounterFlow.StrideReads test stride length)
    (step : ∀ (current : PanSemStateFiniteExact 64 Guest.HostMemory) index,PrefixedReady current key out leading length index 0 → index+stride≤length →
      ∃ next,evaluateHOLFiniteState current loopBody=(none,next) ∧ PrefixedReady next key out leading length (index+stride) 0 ∧ next.clock=current.clock)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (ready : PrefixedReady source key out leading length index 0) (enough : length-index≤source.clock) :
    ∃ post next paid,evaluateHOLFiniteState source (.while test loopBody)=(none,post) ∧
      PrefixedReady post key out leading length next 0 ∧ length-next<stride ∧ paid≤length-index ∧ post.clock=source.clock-paid := by
  generalize rankEq : length-index=rank
  induction rank using Nat.strongRecOn generalizing source index with
  | ind rank ih=>
    have inside : index≤length:=by have bound:=ready.inside; omega
    have small:=ready.small
    have number : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have actual:=reads source (BitVec.ofNat 64 index) ready.indexCell ready.lengthCell (by rw [number]; exact inside)
    rw [number] at actual
    by_cases active : index+stride≤length
    · have entering : eval source test=some (.val (.word 1#64)):=by simpa only [if_pos active,eval,evalHOLFinite] using actual
      have funded : source.clock≠0:=by omega
      let entry:=decClockHOLFinite source
      have entryReady : PrefixedReady entry key out leading length index 0:=
        PrefixedReady.with_clock source key out leading length index 0 (source.clock-1) ready
      obtain ⟨middle,bodyRun,middleReady,middleClock⟩:=step entry index entryReady active
      change middle.clock=source.clock-1 at middleClock
      obtain ⟨post,next,paid,tailRun,postReady,remainder,bound,clock⟩:=
        ih (length-(index+stride)) (by omega) middle (index+stride) middleReady (by omega) rfl
      have run : evaluateHOLFiniteState source (.while test loopBody)=evaluateHOLFiniteState middle (.while test loopBody):=by
        rw [evaluateHOLFiniteState_while_total]
        simp only [eval,evalHOLFinite] at entering ⊢
        rw [entering]
        simp only
        rw [if_pos (show (1#64 : BitVec 64)≠0 from by decide),if_neg funded,bodyRun]
        simp only
        rw [StateSteps.fixed_clock entry middle none (by change middle.clock≤source.clock-1; omega)]
      refine ⟨post,next,paid+1,run.trans tailRun,postReady,remainder,by omega,?_⟩
      rw [clock,middleClock,Nat.sub_sub]
      congr 1
      omega
    · have stopped : eval source test=some (.val (.word 0#64)):=by simpa only [if_neg active,eval,evalHOLFinite] using actual
      have run : evaluateHOLFiniteState source (.while test loopBody)=(none,source):=by
        rw [evaluateHOLFiniteState_while_total]
        simp only [eval,evalHOLFinite] at stopped ⊢
        rw [stopped]
        rfl
      exact ⟨source,index,0,run,ready,by omega,by omega,by simp⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.prefixed_loop_execute
