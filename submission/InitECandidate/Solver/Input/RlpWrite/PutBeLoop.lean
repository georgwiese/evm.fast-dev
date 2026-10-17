import InitECandidate.Solver.Input.RlpWrite.PutBeProgram

namespace InitECandidate.Solver.Input.RlpWrite.PutBe
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem step_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst value : BitVec 64) (index : Nat) (name : String)
    (iNe : ofString "i"≠ofString name) (vNe : ofString "v"≠ofString name) :
    (step source dst value index).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "v" name _ vNe).trans (bind_lookup_other _ "i" name _ iNe)

/-- Complete actual reverse byte-writing loop, exact one-clock payment per
written byte, and a frame for every word outside its aligned store cells. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst value : BitVec 64) (count : Nat) (small : count<2^64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 count))))
    (v : source.locals.lookup (ofString "v")=some (.val (.word value)))
    (mapped : ∀ index<count,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : count≤source.clock) :
    ∃ target,evaluateHOLFiniteState source loop=(none,target) ∧
      target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-count} ∧
      target.locals.lookup (ofString "i")=some (.val (.word 0#64)) ∧
      (∀ name : String,ofString "i"≠ofString name→ ofString "v"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      (∀ query,(∀ index<count,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→target.memory query=source.memory query) := by
  classical
  induction count generalizing source value with
  | zero=>
    have readTest : eval source test=some (.val (.word 0#64)) := by
      simp [eval,test,localVar,evalHOLExact,toExact,i,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have bridge : evalHOLFinite source test=eval source test :=
      congrArg (fun h : DecidablePred source.memaddrs=>@evalHOLExact 64 Guest.HostMemory _ source.toExact h test) (Subsingleton.elim _ _)
    have finiteTest:=bridge.trans readTest
    refine ⟨source,?_,by simp,i,by intros; rfl,by intros; rfl⟩
    rw [loop,evaluateHOLFiniteState_while_total,finiteTest]
    simp
  | succ count ih=>
    have number : (BitVec.ofNat 64 (count+1)).toNat=count+1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    have readTest : eval source test=some (.val (.word 1#64)) := by
      simp [eval,test,localVar,evalHOLExact,toExact,i,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,number]
    let entry:=decClockHOLFinite source
    have bodyRun:=step_execute entry dst value count small d i v (mapped count (by omega))
    let next:=step entry dst value count
    have nextState : next={entry with locals:=next.locals,memory:=next.memory}:=rfl
    have nextClock : next.clock=source.clock-1:=rfl
    have nextD : next.locals.lookup (ofString "dst")=some (.val (.word dst)) :=
      (step_other entry dst value count "dst" (by decide) (by decide)).trans d
    have nextI : next.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 count))) :=
      (bind_lookup_other _ "v" "i" _ (by decide)).trans (bind_lookup_same _ _ _)
    have nextV : next.locals.lookup (ofString "v")=some (.val (.word (value >>> (8:Nat)))):=bind_lookup_same _ _ _
    obtain ⟨target,tailRun,targetState,finalI,others,memory⟩:=ih next (value >>> (8:Nat)) (by omega) nextD nextI nextV (by intro index inside; exact mapped index (by omega)) (by omega)
    have resumed:=while_active source next test loopBody none readTest (by omega) bodyRun (by omega)
    have actual : evaluateHOLFiniteState source loop=(none,target) := by
      change evaluateHOLFiniteState source (.while test loopBody)=_
      change evaluateHOLFiniteState next (.while test loopBody)=_ at tailRun
      exact resumed.trans tailRun
    refine ⟨target,actual,?_,finalI,?_,?_⟩
    · rw [nextState] at targetState
      change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-1-count} at targetState
      have subtract : source.clock-1-count=source.clock-(count+1) := by omega
      simpa only [subtract] using targetState
    · intro name iNe vNe
      exact (others name iNe vNe).trans (step_other entry dst value count name iNe vNe)
    · intro query away
      have tailFrame:=memory query (by intro index inside; exact away index (by omega))
      have firstFrame:=WitnessRadix.ByteStore.away source.memory source.be (dst+BitVec.ofNat 64 count) query (BitVec.ofNat 8 value.toNat) (away count (by omega))
      exact tailFrame.trans firstFrame

end InitECandidate.Solver.Input.RlpWrite.PutBe

#print axioms InitECandidate.Solver.Input.RlpWrite.PutBe.loop_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.PutBe.step_other
