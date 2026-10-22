import InitECandidate.Solver.Input.GuardedCounterLoop
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostCurrentConditional

namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

abbrev Invariant := Input.GuardedCounterLoop.Invariant 32

/-- A finite composition of actual original read-only decisions and small
counter loops. Unmapped reads may exit early; no mapped-operand premise is
used by the cost or its normal current-counter preservation. -/
structure Model (program : ProgHOL 64) (price : Nat) (length : Nat := 32) : Prop where
  cost : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,Input.GuardedCounterLoop.Invariant length source → source.clock-(evaluateHOLFiniteState source program).2.clock≤price
  normal : ∀ source post : PanSemStateFiniteExact 64 Guest.HostMemory,Input.GuardedCounterLoop.Invariant length source → evaluateHOLFiniteState source program=(none,post) → Input.GuardedCounterLoop.Invariant length post

theorem Model.decision {program : ProgHOL 64} (pure : Input.PureDecision program) {length : Nat} : Model program 0 length := by
  constructor
  · intro source valid
    exact Input.ClockCost.of_quiet source.code program (pure.quiet source.code) source rfl
  · intro source post valid run
    have info:=pure.summary source
    rw [run] at info
    have same : post=source := info.1 rfl
    exact same ▸ valid

theorem Model.sequence {first second : ProgHOL 64} {firstPrice secondPrice length : Nat}
    (front : Model first firstPrice length) (back : Model second secondPrice length) : Model (.seq first second) (firstPrice+secondPrice) length := by
  constructor
  · intro source valid
    exact Input.ClockCost.sequence_reached_current source first second firstPrice secondPrice (front.cost source valid)
      (fun middle normal=>back.cost middle (front.normal source middle valid normal))
  · intro source post valid run
    obtain ⟨middle,firstRun,secondRun⟩ := Input.sequence_none source post first second run
    exact back.normal middle post (front.normal source middle valid firstRun) secondRun

theorem Model.conditional (test : ExpHOL 64) {yes no : ProgHOL 64} {yesPrice noPrice length : Nat}
    (left : Model yes yesPrice length) (right : Model no noPrice length) : Model (.ite test yes no) (max yesPrice noPrice) length := by
  constructor
  · intro source valid
    exact Input.ClockCost.conditional_current source test yes no yesPrice noPrice (left.cost source valid) (right.cost source valid)
  · intro source post valid run
    rw [evaluateHOLFiniteState_ite] at run
    generalize read : @evalHOLExact 64 Guest.HostMemory _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query)) test=observed at run
    cases observed with
    | none=>cases run
    | some value=>
      cases value with
      | rStruct fields=>cases run
      | nStruct name fields=>cases run
      | val payload=>
        cases payload with
        | word word=>
          simp only at run
          by_cases zero : word=0
          · rw [if_pos zero] at run
            exact right.normal source post valid run
          · rw [if_neg zero] at run
            exact left.normal source post valid run

theorem Model.loop (test : ExpHOL 64) (body : ProgHOL 64) (stride : Nat) (positive : 0<stride)
    (guarded : Input.GuardedCounter stride body) {length : Nat}
    (testReads : Input.GuardedCounterLoop.TestReads test stride length) (small : length≤64) : Model (.while test body) length length :=
  ⟨fun source valid=>Input.GuardedCounterLoop.cost test body stride length positive small guarded testReads source valid,
    fun source post valid run=>Input.GuardedCounterLoop.normal test body stride length positive small guarded testReads source post valid run⟩

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.MutableTable.MemeqAny.Model.decision
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.Model.sequence
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.Model.conditional
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.Model.loop
