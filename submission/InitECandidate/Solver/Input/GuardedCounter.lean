import InitECandidate.Solver.Input.PureDecision
import InitECandidate.Solver.Input.LoopNormal
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual read-only tests followed by one original i-counter increment.
Tests may fail or return early; successful fallthrough derives its update. -/
inductive GuardedCounter (stride : Nat) : ProgHOL 64→Prop where
  | increment : GuardedCounter stride (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const (BitVec.ofNat 64 stride)]))
  | checks {first rest : ProgHOL 64} (decision : PureDecision first) (tail : GuardedCounter stride rest) : GuardedCounter stride (.seq first rest)

theorem GuardedCounter.normal {program : ProgHOL 64} {stride : Nat} (guarded : GuardedCounter stride program)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (cell : source.locals.lookup (ofString "i")=some (.val (.word word)))
    (normal : evaluateHOLFiniteState source program=(none,post)) : post=bind source "i" (word+BitVec.ofNat 64 stride) := by
  induction guarded generalizing source post with
  | increment=>
    have read : eval source (.op .add [.var .local (ofString "i"),.const (BitVec.ofNat 64 stride)])=some (.val (.word (word+BitVec.ofNat 64 stride))) := by
      simp [eval,evalHOLExact,evalListHOLExact,toExact,cell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have actual:=WitnessRadix.StateSteps.assign_execute source "i" _ word (word+BitVec.ofNat 64 stride) cell read
    exact (congrArg Prod.snd (normal.symm.trans actual))
  | checks decision tail ih=>
    obtain ⟨middle,front,back⟩ := sequence_none source post _ _ normal
    have info:=decision.summary source
    rw [front] at info
    have same : middle=source := info.1 rfl
    subst middle
    exact ih source post cell back

theorem GuardedCounter.quiet {program : ProgHOL 64} {stride : Nat} (guarded : GuardedCounter stride program) (code) : QuietClock.Preserves code program := by
  induction guarded with
  | increment=>exact QuietClock.assign code _ _
  | checks decision tail ih=>exact QuietClock.sequence code _ _ (decision.quiet code) ih

theorem GuardedCounter.no_control {program : ProgHOL 64} {stride : Nat} (guarded : GuardedCounter stride program)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source program).1≠some .break ∧ (evaluateHOLFiniteState source program).1≠some .continue := by
  induction guarded generalizing source with
  | increment=>
    exact ((LocalPrefix.assign (key:=ofString "n") (ofString "i") _ (by decide)).summary_full source).2.2
  | checks decision tail ih=>
    rw [evaluateHOLFiniteState_seq_line780]
    have info:=decision.summary source
    generalize computed : evaluateHOLFiniteState source _=output at info ⊢
    obtain ⟨result,middle⟩ := output
    cases result with
    | none=>exact ih middle
    | some result=>exact info.2

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.GuardedCounter.normal
#print axioms InitECandidate.Solver.Input.GuardedCounter.quiet
#print axioms InitECandidate.Solver.Input.GuardedCounter.no_control
