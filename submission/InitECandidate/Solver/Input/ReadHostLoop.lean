import InitECandidate.Solver.Input.ReadHostEffects
import Mathlib.Data.Nat.Init

namespace InitECandidate.Solver.Input.ReadHostEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Read-only host loop effects hold at every clock, including timeout, break,
continue and exceptional outcomes. This proves no iteration-count bound. -/
theorem loop (code) (test : ExpHOL 64) (body : ProgHOL 64) (pureBody : Preserves code body) :
    Preserves code (.while test body) := by
  classical
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory), source.clock = clock → source.code = code → source.ffi.oracle = InitE.sourceOracle →
      host (evaluateHOLFiniteState source (.while test body)).2 = host source := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro source clockEq installed oracle
      rw [evaluateHOLFiniteState_while_total]
      generalize observed : @evalHOLFinite 64 Guest.HostMemory _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) test = value
      cases value with
      | none => rfl
      | some value =>
        cases value with
        | rStruct fields => rfl
        | nStruct name fields => rfl
        | val payload =>
          cases payload with
          | word word =>
            simp only
            by_cases nonzero : word ≠ 0
            · rw [if_pos nonzero]
              by_cases zero : source.clock = 0
              · rw [if_pos zero]
                rfl
              · rw [if_neg zero]
                have bodyFrame := pureBody (decClockHOLFinite source) installed oracle
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body = output at bodyFrame bodyClock ⊢
                obtain ⟨result, target⟩ := output
                have fixed := WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result bodyClock
                simp only [fixed]
                have targetCode : target.code = code :=
                  (evaluation_fields (decClockHOLFinite source) target body result computed).2.2.2.trans installed
                have targetOracle : target.ffi.oracle = InitE.sourceOracle :=
                  (evaluation_oracle (decClockHOLFinite source) target body result computed).trans oracle
                have earlier : target.clock < clock := by change target.clock ≤ source.clock - 1 at bodyClock; omega
                have tailFrame := ih target.clock earlier target rfl targetCode targetOracle
                cases result with
                | none => exact tailFrame.trans bodyFrame
                | some result =>
                  cases result <;> first | exact tailFrame.trans bodyFrame | exact bodyFrame
            · rw [if_neg nonzero]
  intro source installed oracle
  exact auxiliary source.clock source rfl installed oracle

end InitECandidate.Solver.Input.ReadHostEffects

#print axioms InitECandidate.Solver.Input.ReadHostEffects.loop
