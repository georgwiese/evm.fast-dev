import InitECandidate.Solver.Input.NormalHostEffects
import Mathlib.Data.Nat.Init

namespace InitECandidate.Solver.Input.NormalHostEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A loop which resumes preserves host memory when every resuming body
does. This allows normal break/continue and does not assert a runtime bound. -/
theorem loop (code) (test : ExpHOL 64) (body : ProgHOL 64)
    (pureBody : Preserves code body) : Preserves code (.while test body) := by
  classical
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory), source.clock = clock → source.code = code →
      Resumes (evaluateHOLFiniteState source (.while test body)).1 →
      host (evaluateHOLFiniteState source (.while test body)).2 = host source := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro source clockEq installed resumes
      rw [evaluateHOLFiniteState_while_total] at resumes ⊢
      generalize observed : @evalHOLFinite 64 Guest.HostMemory _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) test = value at resumes ⊢
      cases value with
      | none => rfl
      | some value =>
        cases value with
        | rStruct fields => rfl
        | nStruct name fields => rfl
        | val payload =>
          cases payload with
          | word word =>
            simp only at resumes ⊢
            by_cases nonzero : word ≠ 0
            · rw [if_pos nonzero] at resumes ⊢
              by_cases zero : source.clock = 0
              · rw [if_pos zero]; rfl
              · rw [if_neg zero] at resumes ⊢
                have bodyFrame := pureBody (decClockHOLFinite source) installed
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
                | none => exact (tailFrame resumes).trans (bodyFrame trivial)
                | some result =>
                  cases result with
                  | «break» => exact bodyFrame trivial
                  | «continue» => exact (tailFrame resumes).trans (bodyFrame trivial)
                  | returned value => exact bodyFrame trivial
                  | error | timeOut | exception identifier payload | finalFfi event => cases resumes
            · rw [if_neg nonzero]
  intro source installed resumes
  exact auxiliary source.clock source rfl installed resumes

end InitECandidate.Solver.Input.NormalHostEffects

#print axioms InitECandidate.Solver.Input.NormalHostEffects.loop
