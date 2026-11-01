import InitECandidate.Solver.Input.ClockCostLoop
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Function.Iterate

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

namespace FiniteWalk

/-- A deterministic control transition. `none` is an absorbing exit. This
model applies only after the actual program's control transitions have been
related to `next`; it does not posit termination of an arbitrary program. -/
def advance {α : Type} (next : α → Option α) (current : Option α) : Option α :=
  current.bind next

def Terminates {α : Type} (next : α → Option α) (node : α) : Prop :=
  ∃ ticks, (advance next)^[ticks] (some node) = none

noncomputable def distance {α : Type} (next : α → Option α) (node : α) : Nat := by
  classical
  exact if ended : Terminates next node then Nat.find ended else 0

theorem distance_eq_find {α : Type} {next : α → Option α} {node : α}
    (ended : Terminates next node) : distance next node = Nat.find ended := by
  simp only [distance, dif_pos ended]

theorem distance_spec {α : Type} {next : α → Option α} {node : α}
    (ended : Terminates next node) :
    (advance next)^[distance next node] (some node) = none := by
  rw [distance_eq_find ended]
  exact Nat.find_spec ended

theorem distance_min {α : Type} {next : α → Option α} {node : α}
    (ended : Terminates next node) {ticks : Nat}
    (exit : (advance next)^[ticks] (some node) = none) : distance next node ≤ ticks := by
  rw [distance_eq_find ended]
  exact Nat.find_min' ended exit

theorem distance_pos {α : Type} {next : α → Option α} {node : α}
    (ended : Terminates next node) : 0 < distance next node := by
  have exit := distance_spec ended
  by_contra zero
  have zero : distance next node = 0 := by omega
  rw [zero] at exit
  cases exit

theorem terminates_prepend {α : Type} {next : α → Option α} {node child : α}
    (edge : next node = some child) (ended : Terminates next child) :
    Terminates next node := by
  obtain ⟨ticks, exit⟩ := ended
  refine ⟨ticks + 1, ?_⟩
  simpa only [Function.iterate_succ_apply, advance, Option.bind_some, edge] using exit

theorem terminates_tail {α : Type} {next : α → Option α} {node child : α}
    (edge : next node = some child) (ended : Terminates next node) :
    Terminates next child := by
  obtain ⟨ticks, exit⟩ := ended
  cases ticks with
  | zero => cases exit
  | succ ticks =>
    refine ⟨ticks, ?_⟩
    simpa only [Function.iterate_succ_apply, advance, Option.bind_some, edge] using exit

/-- A real continuing transition decreases the least remaining exit distance
by exactly one, even when no ordering of node bit positions is known. -/
theorem distance_step {α : Type} {next : α → Option α} {node child : α}
    (edge : next node = some child) (ended : Terminates next node) :
    distance next node = distance next child + 1 := by
  have childEnded := terminates_tail edge ended
  have childExit := distance_spec childEnded
  have upper : distance next node ≤ distance next child + 1 :=
    distance_min ended (by
      simpa only [Function.iterate_succ_apply, advance, Option.bind_some, edge] using childExit)
  have positive := distance_pos ended
  have exit := distance_spec ended
  obtain ⟨ticks, length⟩ := Nat.exists_eq_succ_of_ne_zero (show distance next node ≠ 0 by omega)
  rw [length] at exit
  have tailExit : (advance next)^[ticks] (some child) = none := by
    simpa only [Function.iterate_succ_apply, advance, Option.bind_some, edge] using exit
  have lower := distance_min childEnded tailExit
  omega

theorem distance_exit {α : Type} {next : α → Option α} {node : α}
    (exit : next node = none) : Terminates next node ∧ distance next node = 1 := by
  have ended : Terminates next node := ⟨1, by simpa only [Function.iterate_one, advance, Option.bind_some] using exit⟩
  refine ⟨ended, ?_⟩
  have upper : distance next node ≤ 1 := distance_min ended
    (by simpa only [Function.iterate_one, advance, Option.bind_some] using exit)
  have positive := distance_pos ended
  omega

/-- A terminating deterministic walk visits each control at most once before
exit. Its distance is bounded by the number of possible controls. Finiteness
alone does not supply the `ended` premise. -/
theorem distance_le_card {α : Type} [Fintype α] {next : α → Option α} {node : α}
    (ended : Terminates next node) : distance next node ≤ Fintype.card α := by
  classical
  let length := distance next node
  have exit : (advance next)^[length] (some node) = none := distance_spec ended
  have noRepeat : ∀ i j : Fin (length + 1), i.val < j.val →
      (advance next)^[i.val] (some node) ≠ (advance next)^[j.val] (some node) := by
    intro i j earlier same
    have shifted := congrArg ((advance next)^[length - j.val]) same
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at shifted
    have endIndex : length - j.val + j.val = length := by omega
    rw [endIndex, exit] at shifted
    have minimal := distance_min ended shifted
    change length ≤ length - j.val + i.val at minimal
    omega
  have injective : Function.Injective
      (fun i : Fin (length + 1) => (advance next)^[i.val] (some node)) := by
    intro i j same
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with earlier | equal | later
    · exact False.elim (noRepeat i j earlier same)
    · exact equal
    · exact False.elim (noRepeat j i later same.symm)
  have bounded := Fintype.card_le_of_injective _ injective
  simpa only [Fintype.card_fin, Fintype.card_option, Nat.add_le_add_iff_right] using bounded

end FiniteWalk

/-- Amortize an actual non-timeout loop by a current-state allowance.
The same observed execution derives non-timeout body and recursive runs;
no future successful return or per-iteration trace is assumed. -/
theorem potential_loop_terminating (code) (test : ExpHOL 64) (body : ProgHOL 64)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (allowance : PanSemStateFiniteExact 64 Guest.HostMemory → Nat)
    (step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code=code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) →
      word≠0 → current.clock≠0 →
      let output := evaluateHOLFiniteState (decClockHOLFinite current) body
      output.1≠some .timeOut → current.clock-output.2.clock≤allowance current ∧
      ((output.1=none ∨ output.1=some .continue) → invariant output.2 ∧
        current.clock-output.2.clock+allowance output.2≤allowance current))
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : source.code=code) (valid : invariant source)
    (notTimeout : (evaluateHOLFiniteState source (.while test body)).1≠some .timeOut) :
    source.clock-(evaluateHOLFiniteState source (.while test body)).2.clock≤allowance source := by
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory),
      current.clock=clock → current.code=code → invariant current →
      (evaluateHOLFiniteState current (.while test body)).1≠some .timeOut →
      current.clock-(evaluateHOLFiniteState current (.while test body)).2.clock≤allowance current := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro current clockEq installed valid notTimeout
      rw [evaluateHOLFiniteState_while_total] at notTimeout ⊢
      generalize observed : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=value at notTimeout ⊢
      cases value with
      | none => simp
      | some value =>
        cases value with
        | rStruct fields => simp
        | nStruct name fields => simp
        | val payload =>
          cases payload with
          | word word =>
            simp only at notTimeout ⊢
            by_cases nonzero : word≠0
            · rw [if_pos nonzero] at notTimeout ⊢
              by_cases zero : current.clock=0
              · rw [if_pos zero]
                simp [zero]
              · rw [if_neg zero] at notTimeout ⊢
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite current) body=output at bodyClock notTimeout ⊢
                obtain ⟨result,target⟩ := output
                rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite current) target result bodyClock] at notTimeout ⊢
                have bodyNotTimeout : result≠some .timeOut := by
                  intro timed
                  subst result
                  exact notTimeout rfl
                have budget := step current installed valid word observed nonzero zero
                rw [computed] at budget
                have budget := budget bodyNotTimeout
                have stopped : current.clock-target.clock≤allowance current := budget.1
                have tail : (result=none ∨ result=some .continue) →
                    current.clock-(evaluateHOLFiniteState target (.while test body)).2.clock≤allowance current := by
                  intro continuing
                  have tailNotTimeout : (evaluateHOLFiniteState target (.while test body)).1≠some .timeOut := by
                    rcases continuing with normal | continued <;> subst result <;> exact notTimeout
                  obtain ⟨targetValid,paid⟩ := budget.2 continuing
                  change current.clock-target.clock+allowance target≤allowance current at paid
                  change target.clock≤current.clock-1 at bodyClock
                  have targetCode := (Input.evaluation_fields (decClockHOLFinite current) target body result computed).2.2.2.trans installed
                  have earlier : target.clock<clock := by change target.clock≤current.clock-1 at bodyClock; omega
                  have priced := ih target.clock earlier target rfl targetCode targetValid tailNotTimeout
                  have tailClock := evaluateHOLFiniteState_clock_le target (.while test body)
                  omega
                cases result with
                | none => exact tail (Or.inl rfl)
                | some result => cases result <;> first | exact tail (Or.inr rfl) | exact stopped
            · rw [if_neg nonzero]
              simp
  exact auxiliary source.clock source rfl codeEq valid notTimeout

/-- Relate a real non-timeout loop to a deterministic control walk. The exit
path is extracted from that same execution, rather than assumed as a future
successful return. All control observations, including aborting bodies, must
be established from the actual program. -/
theorem control_loop_terminating {α : Type} (code) (test : ExpHOL 64) (body : ProgHOL 64)
    (price : Nat) (priced : Bound code body price)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (control : PanSemStateFiniteExact 64 Guest.HostMemory → α) (next : α → Option α)
    (inactive : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code = code → invariant current →
      (¬ ∃ word : BitVec 64,
        evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) test = some (.val (.word word)) ∧ word ≠ 0) →
      next (control current) = none)
    (transitions : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code = code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) test = some (.val (.word word)) →
      word ≠ 0 → current.clock ≠ 0 →
      let output := evaluateHOLFiniteState (decClockHOLFinite current) body
      ((output.1 = none ∨ output.1 = some .continue) →
        invariant output.2 ∧ next (control current) = some (control output.2)) ∧
      (¬ (output.1 = none ∨ output.1 = some .continue) → next (control current) = none))
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : source.code = code)
    (valid : invariant source)
    (notTimeout : (evaluateHOLFiniteState source (.while test body)).1 ≠ some .timeOut) :
    FiniteWalk.Terminates next (control source) ∧
    source.clock - (evaluateHOLFiniteState source (.while test body)).2.clock ≤
      (price + 1) * FiniteWalk.distance next (control source) := by
  classical
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory),
      current.clock = clock → current.code = code → invariant current →
      (evaluateHOLFiniteState current (.while test body)).1 ≠ some .timeOut →
      FiniteWalk.Terminates next (control current) ∧
      current.clock - (evaluateHOLFiniteState current (.while test body)).2.clock ≤
        (price + 1) * FiniteWalk.distance next (control current) := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro current clockEq installed valid notTimeout
      by_cases active : ∃ word : BitVec 64,
          evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) test = some (.val (.word word)) ∧ word ≠ 0
      · obtain ⟨word, read, nonzero⟩ := active
        rw [evaluateHOLFiniteState_while_total, read] at notTimeout ⊢
        simp only [if_pos nonzero] at notTimeout ⊢
        by_cases zero : current.clock = 0
        · rw [if_pos zero] at notTimeout
          exact False.elim (notTimeout rfl)
        · rw [if_neg zero] at notTimeout ⊢
          have model := transitions current installed valid word read nonzero zero
          have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
          have bodyCost := priced (decClockHOLFinite current) installed
          generalize computed : evaluateHOLFiniteState (decClockHOLFinite current) body = output at model bodyClock bodyCost notTimeout ⊢
          obtain ⟨result, target⟩ := output
          rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite current) target result bodyClock] at notTimeout ⊢
          change target.clock ≤ current.clock - 1 at bodyClock
          change current.clock - 1 - target.clock ≤ price at bodyCost
          have spent : current.clock - target.clock ≤ price + 1 := by omega
          have stopped : ¬ (result = none ∨ result = some .continue) →
              FiniteWalk.Terminates next (control current) ∧
              current.clock - target.clock ≤ (price + 1) * FiniteWalk.distance next (control current) := by
            intro halted
            obtain ⟨ended, distance⟩ := FiniteWalk.distance_exit (model.2 halted)
            exact ⟨ended, by simpa only [distance, Nat.mul_one] using spent⟩
          have tail : (result = none ∨ result = some .continue) →
              FiniteWalk.Terminates next (control current) ∧
              current.clock - (evaluateHOLFiniteState target (.while test body)).2.clock ≤
                (price + 1) * FiniteWalk.distance next (control current) := by
            intro continuing
            have tailNotTimeout : (evaluateHOLFiniteState target (.while test body)).1 ≠ some .timeOut := by
              rcases continuing with normal | continued <;> subst result <;> exact notTimeout
            obtain ⟨targetValid, edge⟩ := model.1 continuing
            change next (control current) = some (control target) at edge
            have targetCode := (Input.evaluation_fields (decClockHOLFinite current) target body result computed).2.2.2.trans installed
            have earlier : target.clock < clock := by omega
            obtain ⟨targetEnded, targetCost⟩ := ih target.clock earlier target rfl targetCode targetValid tailNotTimeout
            have ended := FiniteWalk.terminates_prepend edge targetEnded
            have distance := FiniteWalk.distance_step edge ended
            have tailClock := evaluateHOLFiniteState_clock_le target (.while test body)
            refine ⟨ended, ?_⟩
            rw [distance, Nat.mul_add, Nat.mul_one]
            omega
          cases result with
          | none => exact tail (Or.inl rfl)
          | some result =>
            cases result <;> first | exact tail (Or.inr rfl) | exact stopped (by simp)
      · obtain ⟨ended, distance⟩ := FiniteWalk.distance_exit (inactive current installed valid active)
        refine ⟨ended, ?_⟩
        have unchanged : (evaluateHOLFiniteState current (.while test body)).2.clock = current.clock := by
          rw [evaluateHOLFiniteState_while_total]
          generalize observed : evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) test = value
          cases value with
          | none => rfl
          | some value =>
            cases value with
            | rStruct fields => rfl
            | nStruct name fields => rfl
            | val payload =>
              cases payload with
              | word word =>
                have zero : word = 0 := by
                  by_contra nonzero
                  exact active ⟨word, observed, nonzero⟩
                simp only [zero, ne_eq, not_true_eq_false, if_false]
        rw [unchanged, Nat.sub_self]
        exact Nat.zero_le _
  exact auxiliary source.clock source rfl codeEq valid notTimeout

/-- Finitely many deterministic controls bound a real non-timeout loop.
This supplies a clock allowance without requiring an increasing bit image;
the program-specific finite control model remains an explicit obligation. -/
theorem finite_control_loop_terminating {α : Type} [Fintype α] (code) (test : ExpHOL 64) (body : ProgHOL 64)
    (price : Nat) (priced : Bound code body price)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (control : PanSemStateFiniteExact 64 Guest.HostMemory → α) (next : α → Option α)
    (inactive : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code = code → invariant current →
      (¬ ∃ word : BitVec 64,
        evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) test = some (.val (.word word)) ∧ word ≠ 0) →
      next (control current) = none)
    (transitions : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code = code → invariant current → ∀ word : BitVec 64,
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) test = some (.val (.word word)) →
      word ≠ 0 → current.clock ≠ 0 →
      let output := evaluateHOLFiniteState (decClockHOLFinite current) body
      ((output.1 = none ∨ output.1 = some .continue) →
        invariant output.2 ∧ next (control current) = some (control output.2)) ∧
      (¬ (output.1 = none ∨ output.1 = some .continue) → next (control current) = none))
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : source.code = code)
    (valid : invariant source)
    (notTimeout : (evaluateHOLFiniteState source (.while test body)).1 ≠ some .timeOut) :
    source.clock - (evaluateHOLFiniteState source (.while test body)).2.clock ≤
      (price + 1) * Fintype.card α := by
  obtain ⟨ended, paid⟩ := control_loop_terminating code test body price priced invariant control next inactive transitions source codeEq valid notTimeout
  exact paid.trans (Nat.mul_le_mul_left _ (FiniteWalk.distance_le_card ended))

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.potential_loop_terminating

#print axioms InitECandidate.Solver.Input.ClockCost.FiniteWalk.distance_spec
#print axioms InitECandidate.Solver.Input.ClockCost.FiniteWalk.distance_min
#print axioms InitECandidate.Solver.Input.ClockCost.FiniteWalk.distance_pos
#print axioms InitECandidate.Solver.Input.ClockCost.FiniteWalk.terminates_prepend
#print axioms InitECandidate.Solver.Input.ClockCost.FiniteWalk.terminates_tail
#print axioms InitECandidate.Solver.Input.ClockCost.FiniteWalk.distance_step
#print axioms InitECandidate.Solver.Input.ClockCost.FiniteWalk.distance_exit
#print axioms InitECandidate.Solver.Input.ClockCost.FiniteWalk.distance_le_card
#print axioms InitECandidate.Solver.Input.ClockCost.control_loop_terminating
#print axioms InitECandidate.Solver.Input.ClockCost.finite_control_loop_terminating
