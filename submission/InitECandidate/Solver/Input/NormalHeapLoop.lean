import InitECandidate.Solver.Input.NormalHeapEffects
import Mathlib.Data.Nat.Init

namespace InitECandidate.Solver.Input.NormalHeapEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Resuming loop control retains a valid lower heap frontier. Actual
break/continue/returned bodies are included; no runtime bound is asserted. -/
theorem loop (code) (test : ExpHOL 64) (body : ProgHOL 64)
    (pureBody : Preserves code body) : Preserves code (.while test body) := by
  classical
  intro source installed lower initial resumes
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory), source.clock = clock → source.code = code →
      AtLeast lower source → NormalHostEffects.Resumes (evaluateHOLFiniteState source (.while test body)).1 →
      AtLeast lower (evaluateHOLFiniteState source (.while test body)).2 := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro source clockEq installed initial resumes
      rw [evaluateHOLFiniteState_while_total] at resumes ⊢
      generalize observed : @evalHOLFinite 64 Guest.HostMemory _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) test = value at resumes ⊢
      cases value with
      | none => exact initial
      | some value =>
        cases value with
        | rStruct fields => exact initial
        | nStruct name fields => exact initial
        | val payload =>
          cases payload with
          | word word =>
            simp only at resumes ⊢
            by_cases nonzero : word ≠ 0
            · rw [if_pos nonzero] at resumes ⊢
              by_cases zero : source.clock = 0
              · rw [if_pos zero]; exact initial
              · rw [if_neg zero] at resumes ⊢
                have bodyFrame := pureBody (decClockHOLFinite source) installed lower initial
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body = output at bodyFrame bodyClock resumes ⊢
                obtain ⟨result, target⟩ := output
                have fixed := WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result bodyClock
                simp only [fixed] at resumes ⊢
                have fields := evaluation_fields (decClockHOLFinite source) target body result computed
                have targetCode : target.code = code := fields.2.2.2.trans installed
                have earlier : target.clock < clock := by change target.clock ≤ source.clock - 1 at bodyClock; omega
                have tailFrame := ih target.clock earlier target rfl targetCode
                cases result with
                | none => exact tailFrame (bodyFrame trivial) resumes
                | some result =>
                  cases result with
                  | «break» => exact bodyFrame trivial
                  | «continue» => exact tailFrame (bodyFrame trivial) resumes
                  | returned value => exact bodyFrame trivial
                  | error | timeOut | exception identifier payload | finalFfi event => cases resumes
            · rw [if_neg nonzero]; exact initial
  exact auxiliary source.clock source rfl installed initial resumes

end InitECandidate.Solver.Input.NormalHeapEffects

#print axioms InitECandidate.Solver.Input.NormalHeapEffects.loop
