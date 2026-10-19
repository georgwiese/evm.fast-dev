import InitECandidate.Solver.Input.NoNamedException
import InitECandidate.Solver.Input.NoExceptionLoop

namespace InitECandidate.Solver.Input.NoNamedException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Loop safety covers every clock and body outcome; it asserts neither a
bound on iterations nor normal completion. -/
theorem loop (code) (forbidden : MlS) (test : ExpHOL 64) (body : ProgHOL 64) (bodySafe : Safe code forbidden body) : Safe code forbidden (.while test body) := by
  classical
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory), source.clock = clock → source.code = code →
      ∀ payload, (evaluateHOLFiniteState source (.while test body)).1 ≠ some (.exception forbidden payload) := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro source clockEq installed payload
      rw [evaluateHOLFiniteState_while_total]
      generalize observed : @evalHOLFinite 64 Guest.HostMemory _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) test = value
      cases value with
      | none => simp
      | some value =>
        cases value with
        | rStruct fields => simp
        | nStruct name fields => simp
        | val word =>
          cases word with
          | word word =>
            simp only
            by_cases nonzero : word ≠ 0
            · rw [if_pos nonzero]
              by_cases zero : source.clock = 0
              · rw [if_pos zero]; simp
              · rw [if_neg zero]
                have safe := bodySafe (decClockHOLFinite source) installed payload
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body = output at safe bodyClock ⊢
                obtain ⟨result, target⟩ := output
                have fixed := WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result bodyClock
                simp only [fixed]
                have targetCode := (evaluation_fields (decClockHOLFinite source) target body result computed).2.2.2.trans installed
                have earlier : target.clock < clock := by change target.clock ≤ source.clock - 1 at bodyClock; omega
                have tailSafe := ih target.clock earlier target rfl targetCode payload
                cases result with
                | none => exact tailSafe
                | some result =>
                  cases result <;> first | exact tailSafe | exact safe | simp
            · rw [if_neg nonzero]; simp
  intro source installed payload
  exact auxiliary source.clock source rfl installed payload

end InitECandidate.Solver.Input.NoNamedException

#print axioms InitECandidate.Solver.Input.NoNamedException.loop
