import InitECandidate.Solver.Input.RlpWrite.U256MinStep

namespace InitECandidate.Solver.Input.RlpWrite.U256Min
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index length : Nat) (indexBound : index≤32) (lengthBound : length≤32)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source loopTest=some (.val (.word (if index<length then 1#64 else 0#64))) := by
  have indexNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have lengthNumber : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [eval,loopTest,localVar,evalHOLExact,toExact,i,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,indexNumber,lengthNumber]

/-- Every real minimal-U256 byte-writing iteration pays a while tick and one
limb call. No allocated-byte or symbolic shift expression is assumed. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (dst : BitVec 64)
    (index rounds length : Nat) (finish : index+rounds=length) (small : length≤32)
    (a : source.locals.lookup (ofString "a")=some (U256Value.tuple words))
    (outLocal : source.locals.lookup (ofString "out")=some (.val (.word dst)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (code : source.code.lookup (ofString "u256_limb")=some (U256Limb.formals,U256Limb.body,.one))
    (mapped : ∀ offset<length,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 offset))) (enough : 2*rounds≤source.clock) :
    ∃ target,evaluateHOLFiniteState source loop=(none,target) ∧
      target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-2*rounds} ∧
      target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 length))) ∧
      (∀ name : String,ofString "i"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      (∀ query,(∀ offset<length,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 offset))→target.memory query=source.memory query) := by
  classical
  induction rounds generalizing source index with
  | zero=>
    have inactive : ¬index<length := by omega
    have read:=loop_test_read source index length (by omega) small i n
    simp only [if_neg inactive] at read
    have bridge : evalHOLFinite source loopTest=eval source loopTest :=
      congrArg (fun h : DecidablePred source.memaddrs=>@evalHOLExact 64 Guest.HostMemory _ source.toExact h loopTest) (Subsingleton.elim _ _)
    have finiteTest:=bridge.trans read
    refine ⟨source,?_,by simp,by simpa only [show index=length from by omega] using i,by intros; rfl,by intros; rfl⟩
    rw [loop,evaluateHOLFiniteState_while_total,finiteTest]
    simp
  | succ rounds ih=>
    have active : index<length := by omega
    have read:=loop_test_read source index length (by omega) small i n
    simp only [if_pos active] at read
    let entry:=decClockHOLFinite source
    obtain ⟨memory,bodyRun,bodyFrame⟩:=step_execute entry words dst index length active small a outLocal i n code (mapped index active) (by change 1≤source.clock-1; omega)
    let next:=bind {entry with memory:=memory,clock:=entry.clock-1} "i" (BitVec.ofNat 64 (index+1))
    have nextState : next={source with locals:=next.locals,memory:=memory,clock:=source.clock-1-1}:=rfl
    have nextClock : next.clock=source.clock-1-1:=rfl
    have nextA : next.locals.lookup (ofString "a")=some (U256Value.tuple words):=
      (bind_lookup_other _ "i" "a" _ (by decide)).trans a
    have nextOut : next.locals.lookup (ofString "out")=some (.val (.word dst)):=
      (bind_lookup_other _ "i" "out" _ (by decide)).trans outLocal
    have nextN : next.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))):=
      (bind_lookup_other _ "i" "len" _ (by decide)).trans n
    have nextI : next.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))):=bind_lookup_same _ _ _
    obtain ⟨target,tailRun,frame,finalI,others,tailMemory⟩:=ih next (index+1) (by omega) nextA nextOut nextI nextN code mapped (by omega)
    have resumed:=while_active source next loopTest loopBody none read (by omega) bodyRun (by omega)
    have actual : evaluateHOLFiniteState source loop=(none,target) := by
      change evaluateHOLFiniteState source (.while loopTest loopBody)=_
      change evaluateHOLFiniteState next (.while loopTest loopBody)=_ at tailRun
      exact resumed.trans tailRun
    refine ⟨target,actual,?_,finalI,?_,?_⟩
    · rw [nextState] at frame
      change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-1-1-2*rounds} at frame
      have subtract : source.clock-1-1-2*rounds=source.clock-2*(rounds+1) := by omega
      simpa only [subtract] using frame
    · intro name different
      exact (others name different).trans (bind_lookup_other _ "i" name _ different)
    · intro query away
      exact (tailMemory query away).trans (bodyFrame query (away index active))

end InitECandidate.Solver.Input.RlpWrite.U256Min

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.loop_test_read
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.loop_execute
