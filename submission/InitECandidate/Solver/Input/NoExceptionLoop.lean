import InitECandidate.Solver.Input.NoException
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input.NoException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem store_byte (code) (address value : ExpHOL 64) : Safe code (.storeByte address value) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_storeByte]
  repeat first | (solve | simp) | split

theorem external (code) (name : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    Safe code (.extCall name configuration configurationLength array arrayLength) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_extCall_source]
  split
  · split
    · split <;> simp
    · simp
  · simp

theorem shared_store (code) (size : OpSize) (address value : ExpHOL 64) : Safe code (.shMemStore size address value) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · simp only [shMemStoreHOLExact]
    split
    · split
      · split <;> simp
      · simp
    · split
      · split <;> simp
      · simp
  · simp

/-- Loop safety covers every clock and body outcome; it asserts neither a
bound on iterations nor normal completion. -/
theorem loop (code) (test : ExpHOL 64) (body : ProgHOL 64) (bodySafe : Safe code body) : Safe code (.while test body) := by
  classical
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory), source.clock = clock → source.code = code →
      ∀ identifier payload, (evaluateHOLFiniteState source (.while test body)).1 ≠ some (.exception identifier payload) := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro source clockEq installed identifier payload
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
                have safe := bodySafe (decClockHOLFinite source) installed identifier payload
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body = output at safe bodyClock ⊢
                obtain ⟨result, target⟩ := output
                have fixed := WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result bodyClock
                simp only [fixed]
                have targetCode := (evaluation_fields (decClockHOLFinite source) target body result computed).2.2.2.trans installed
                have earlier : target.clock < clock := by change target.clock ≤ source.clock - 1 at bodyClock; omega
                have tailSafe := ih target.clock earlier target rfl targetCode identifier payload
                cases result with
                | none => exact tailSafe
                | some result =>
                  cases result <;> first | exact tailSafe | exact safe | simp
            · rw [if_neg nonzero]; simp
  intro source installed identifier payload
  exact auxiliary source.clock source rfl installed identifier payload

end InitECandidate.Solver.Input.NoException

#print axioms InitECandidate.Solver.Input.NoException.store_byte
#print axioms InitECandidate.Solver.Input.NoException.external
#print axioms InitECandidate.Solver.Input.NoException.shared_store
#print axioms InitECandidate.Solver.Input.NoException.loop
