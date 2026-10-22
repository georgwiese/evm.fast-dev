import InitECandidate.Solver.Mpt.KeyToNibblesSmallBlock
import InitECandidate.Solver.Mpt.KeyToNibblesAnyLoops

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem SmallReady.with_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (length index written clock : Nat) (bytes : Nat→BitVec 8) (ready : SmallReady source key out length index written bytes) :
    SmallReady {source with clock:=clock} key out length index written bytes :=
  ⟨ready.keyCell,ready.outCell,ready.indexCell,ready.lengthCell,ready.little,ready.inside,ready.small,
    ready.fits,ready.mapped,ready.input,ready.separate,ready.nibbles⟩

theorem small_tail_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (length index : Nat) (bytes : Nat→BitVec 8) (ready : SmallReady source key out length index 0 bytes)
    (room : index+1≤length) :
    ∃ post,evaluateHOLFiniteState source tailBody=(none,post) ∧ SmallReady post key out length (index+1) 0 bytes ∧
      post.clock=source.clock ∧ OutputFrame source post out := by
  let written:=byteState source "b" 0 out (BitVec.ofNat 64 index) (bytes (index+0))
  have next : SmallReady written key out length index 1 bytes:=
    SmallReady.byte source key out length index 0 bytes ready "b" (by decide) (by decide) (by decide) (by decide) room
  let advanced:=bind written "i" (BitVec.ofNat 64 (index+1))
  have incrementRun : evaluateHOLFiniteState written (increment 1#64)=(none,advanced):=
    SmallReady.increment_execute written key out length index 1 bytes next
  have advancedReady:=SmallReady.advance written key out length index 1 bytes next
  refine ⟨restore source "b" advanced,?_,?_,rfl,⟨rfl,?_⟩⟩
  · rw [tail_body_shape]
    change evaluateHOLFiniteState source (byteStep "b" 0 (increment 1#64))=_
    rw [SmallReady.byte_execute source key out length index 0 bytes ready "b" (by decide) (by decide) room,incrementRun]
  · exact SmallReady.restore source advanced key out length (index+1) 0 bytes advancedReady "b" (by decide) (by decide) (by decide) (by decide)
  · intro query away
    exact SmallReady.byte_memory source key out query length index 0 bytes ready "b" room away

/-- A funded original converter loop consumes its actual bounded input
counter while carrying the physical nibble prefix and byte ownership. -/
theorem small_loop_execute (test : ExpHOL 64) (loopBody : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (key out : BitVec 64) (bytes : Nat→BitVec 8)
    (reads : Input.CounterFlow.StrideReads test stride length)
    (step : ∀ (current : PanSemStateFiniteExact 64 Guest.HostMemory) index,SmallReady current key out length index 0 bytes→index+stride≤length→
      ∃ next,evaluateHOLFiniteState current loopBody=(none,next) ∧ SmallReady next key out length (index+stride) 0 bytes ∧
        next.clock=current.clock ∧ OutputFrame current next out)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (ready : SmallReady source key out length index 0 bytes) (enough : length-index≤source.clock) :
    ∃ post next paid,evaluateHOLFiniteState source (.while test loopBody)=(none,post) ∧
      SmallReady post key out length next 0 bytes ∧ length-next<stride ∧ paid≤length-index ∧
      post.clock=source.clock-paid ∧ OutputFrame source post out := by
  generalize rankEq : length-index=rank
  induction rank using Nat.strongRecOn generalizing source index with
  | ind rank ih=>
    have inside : index≤length:=by have h:=ready.inside; omega
    have small:=ready.small
    have number : (BitVec.ofNat 64 index).toNat=index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have actual:=reads source (BitVec.ofNat 64 index) ready.indexCell ready.lengthCell (by rw [number]; exact inside)
    rw [number] at actual
    by_cases active : index+stride≤length
    · have entering : eval source test=some (.val (.word 1#64)):=by simpa only [if_pos active,eval,evalHOLFinite] using actual
      have funded : source.clock≠0:=by omega
      let entry:=decClockHOLFinite source
      have entryReady : SmallReady entry key out length index 0 bytes:=
        SmallReady.with_clock source key out length index 0 (source.clock-1) bytes ready
      obtain ⟨middle,bodyRun,middleReady,middleClock,bodyFrame⟩:=step entry index entryReady active
      change middle.clock=source.clock-1 at middleClock
      obtain ⟨post,next,paid,tailRun,postReady,remainder,bound,clock,tailFrame⟩:=
        ih (length-(index+stride)) (by omega) middle (index+stride) middleReady (by omega) rfl
      have run : evaluateHOLFiniteState source (.while test loopBody)=evaluateHOLFiniteState middle (.while test loopBody):=by
        rw [evaluateHOLFiniteState_while_total]
        simp only [eval,evalHOLFinite] at entering ⊢
        rw [entering]
        simp only
        rw [if_pos (show (1#64 : BitVec 64)≠0 from by decide),if_neg funded,bodyRun]
        simp only
        rw [StateSteps.fixed_clock entry middle none (by change middle.clock≤source.clock-1; omega)]
      refine ⟨post,next,paid+1,run.trans tailRun,postReady,remainder,by omega,?_,?_⟩
      · rw [clock,middleClock,Nat.sub_sub]
        congr 1
        omega
      · exact OutputFrame.trans source middle post out ⟨bodyFrame.fields,bodyFrame.memory⟩ tailFrame
    · have stopped : eval source test=some (.val (.word 0#64)):=by simpa only [if_neg active,eval,evalHOLFinite] using actual
      have run : evaluateHOLFiniteState source (.while test loopBody)=(none,source):=by
        rw [evaluateHOLFiniteState_while_total]
        simp only [eval,evalHOLFinite] at stopped ⊢
        rw [stopped]
        simp
      exact ⟨source,index,0,run,ready,by omega,by omega,by simp,OutputFrame.refl source out⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SmallReady.with_clock
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.small_tail_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.small_loop_execute
