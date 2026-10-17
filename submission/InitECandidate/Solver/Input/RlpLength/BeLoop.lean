import InitECandidate.Solver.Input.RlpLength.BeStep

namespace InitECandidate.Solver.Input.RlpLength.Be
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (v : source.locals.lookup (ofString "v")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source loop=(none,source) := by
  classical
  have test:=test_read source 0#64 v
  simp only [if_pos rfl] at test
  have bridge : evalHOLFinite source loopTest=eval source loopTest :=
    congrArg (fun h : DecidablePred source.memaddrs=>@evalHOLExact 64 Guest.HostMemory _ source.toExact h loopTest) (Subsingleton.elim _ _)
  rw [loop,evaluateHOLFiniteState_while_total,bridge.trans test]
  simp

/-- The actual repeated byte shift terminates in at most eight rounds.
No source memory, global, FFI or code field changes. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (count rounds : Nat)
    (valueBound : value.toNat<2^(8*rounds)) (countBound : count+rounds≤8) (enough : rounds≤source.clock)
    (v : source.locals.lookup (ofString "v")=some (.val (.word value)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    ∃ target paid,paid≤rounds ∧ evaluateHOLFiniteState source loop=(none,target) ∧
      target={source with locals:=target.locals,clock:=source.clock-paid} ∧
      target.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (count+paid)))) := by
  classical
  induction rounds generalizing source value count with
  | zero=>
    have zero : value=0#64 := by apply BitVec.eq_of_toNat_eq; change value.toNat=0; have small : value.toNat<1:=valueBound; omega
    have run:=loop_zero source (by simpa only [zero] using v)
    refine ⟨source,0,by omega,run,by simp,?_⟩
    simpa using n
  | succ rounds ih=>
    by_cases zero : value=0#64
    · have run:=loop_zero source (by simpa only [zero] using v)
      refine ⟨source,0,by omega,run,by simp,?_⟩
      simpa using n
    · let entry:=decClockHOLFinite source
      let next:=step entry value count
      have stateEq : next={entry with locals:=next.locals}:=step_state entry value count
      have nextClock:=congrArg PanSemStateFiniteExact.clock stateEq
      change next.clock=source.clock-1 at nextClock
      have fields:=step_fields entry value count
      have shiftedBound : (value>>>(8:Nat)).toNat<2^(8*rounds) := by
        rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
        have power : 2^(8*(rounds+1))=2^(8*rounds)*256 := by rw [Nat.mul_add,Nat.mul_one,Nat.pow_add]
        rw [power] at valueBound
        change value.toNat/256<2^(8*rounds)
        omega
      obtain ⟨target,paid,bound,tailRun,targetState,finalN⟩:=ih next (value>>>(8:Nat)) (count+1) shiftedBound (by omega) (by omega) fields.1 fields.2
      have bodyRun:=body_execute entry value count v n
      have test:=test_read source value v
      simp only [if_neg zero] at test
      have resumed:=while_active source next loopTest loopBody none test (by omega) bodyRun (by omega)
      refine ⟨target,paid+1,by omega,resumed.trans tailRun,?_,?_⟩
      · rw [stateEq] at targetState
        change target={source with locals:=target.locals,clock:=source.clock-1-paid} at targetState
        have subtract : source.clock-1-paid=source.clock-(paid+1) := by omega
        simpa only [subtract] using targetState
      · have sum : count+1+paid=count+(paid+1) := by omega
        simpa only [sum] using finalN

end InitECandidate.Solver.Input.RlpLength.Be

#print axioms InitECandidate.Solver.Input.RlpLength.Be.loop_execute
