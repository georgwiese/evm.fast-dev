import InitECandidate.Solver.Input.CurrentVerify.TransactionProgram
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def transactionScanEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (length : Nat) :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "txs" array)
    "ntx" (BitVec.ofNat 64 length)) "i" 0#64

theorem transaction_scan_frame (code) : LocalEffects.Preserves code transactionScan :=
  LocalEffects.loop code _ _ (LocalEffects.sequence code _ _
    (LocalEffects.conditional code _ _ _ (LocalEffects.raised code _ _) (LocalEffects.skip code))
    (LocalEffects.assign code _ _))

/-- The read-only guard and real counter assignment retain every other
caller local through a genuine normal scan. No slice-read success is assumed. -/
theorem transaction_scan_other (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS)
    (other : key≠ofString "i") (run : evaluateHOLFiniteState source transactionScan=(none,post)) :
    post.locals.lookup key=source.locals.lookup key := by
  apply loop_invariant_no_control source.code transactionTest transactionStep transaction_guarded.no_control
    (fun current=>current.locals.lookup key=source.locals.lookup key) _ source post rfl rfl run
  intro current codeEq cell observed read nonzero funded target bodyRun
  obtain ⟨middle,guardRun,incrementRun⟩:=sequence_none (decClockHOLFinite current) target _ _ bodyRun
  have guard : PureDecision emptyTransactionGuard:=.ite _ (.raised _ _) .skip
  have info:=guard.summary (decClockHOLFinite current)
  rw [guardRun] at info
  have same : middle=decClockHOLFinite current:=info.1 rfl
  subst middle
  have summary:=(LocalPrefix.assign (ofString "i") (.op .add [localVar "i",.const 1#64]) other).summary_full (decClockHOLFinite current)
  unfold LocalSummary at summary
  change evaluateHOLFiniteState (decClockHOLFinite current) (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]))=(none,target) at incrementRun
  rw [incrementRun] at summary
  exact (summary.1 rfl).trans cell

/-- Actual current803 declarations and scan either stop within the real
decoded count or resume at the genuine payload-header suffix with the same
nonlocal state. Every helper failure and timeout remains included. -/
theorem transaction_prefix_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (length : Nat)
    (small : length<2^63)
    (arrayRead : eval source transactionArrayExpression=some (.val (.word array)))
    (countRead : eval (WitnessRadix.QueryBranch.bind source "txs" array) transactionCountExpression=
      some (.val (.word (BitVec.ofNat 64 length))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterStateInit=(outcome,post)) :
    source.clock-post.clock≤length ∨ ∃ current inner,
      LocalEffects.erase current=LocalEffects.erase source ∧
      (∀ key : MlS,key≠ofString "i" → current.locals.lookup key=(transactionScanEntry source array length).locals.lookup key) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤length ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterTransactionScan=(outcome,inner) := by
  rw [transaction_shapes.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip,transaction_shapes.2.1] at run
  obtain ⟨first,firstRun,firstEnd⟩:=ScalarScope.declare_trace source post "txs" transactionArrayExpression array afterTransactionArray outcome arrayRead run
  rw [transaction_shapes.2.2.1] at firstRun
  obtain ⟨second,secondRun,secondEnd⟩:=ScalarScope.declare_trace (WitnessRadix.QueryBranch.bind source "txs" array) first
    "ntx" transactionCountExpression (BitVec.ofNat 64 length) afterTransactionCount outcome countRead firstRun
  let counted:=WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "txs" array) "ntx" (BitVec.ofNat 64 length)
  have zeroRead : eval counted (.const 0#64)=some (.val (.word 0#64)):=by rfl
  rw [transaction_shapes.2.2.2.1] at secondRun
  obtain ⟨third,thirdRun,thirdEnd⟩:=ScalarScope.declare_trace counted second "i" (.const 0#64) 0#64 transactionScanTail outcome zeroRead secondRun
  let entry:=transactionScanEntry source array length
  have counter : entry.locals.lookup (ofString "i")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have count : entry.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other _ "i" "ntx" _ (by decide)).trans (bind_lookup_same _ _ _)
  have priced:=transaction_scan_cost entry length small counter count
  have forward:=evaluateHOLFiniteState_clock_le entry transactionScan
  have frame:=transaction_scan_frame entry.code entry rfl
  have endpoint : post.clock=third.clock:=by rw [firstEnd,secondEnd,thirdEnd]; rfl
  change evaluateHOLFiniteState entry transactionScanTail=(outcome,third) at thirdRun
  rw [transaction_shapes.2.2.2.2,evaluateHOLFiniteState_seq_line780] at thirdRun
  dsimp only at thirdRun
  generalize scanned : evaluateHOLFiniteState entry transactionScan=output at priced forward frame thirdRun
  obtain ⟨result,current⟩:=output
  change source.clock-current.clock≤length at priced
  change current.clock≤source.clock at forward
  change LocalEffects.erase current=LocalEffects.erase source at frame
  cases result with
  | none=>
    change evaluateHOLFiniteState current afterTransactionScan=(outcome,third) at thirdRun
    exact Or.inr ⟨current,third,frame,fun key other=>transaction_scan_other entry current key other scanned,forward,priced,endpoint,thirdRun⟩
  | some result=>
    have clocks:=congrArg (fun output=>output.2.clock) thirdRun
    change current.clock=third.clock at clocks
    exact Or.inl (by rw [endpoint,←clocks]; exact priced)

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.transaction_scan_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.transaction_scan_other
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.transaction_prefix_trace
