import InitECandidate.Solver.GasBudget.ForwardPrefixNormal
import InitECandidate.Solver.GasBudget.FrameSums

namespace InitECandidate.Solver.GasBudget.ForwardPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Lift the actual original forward-gas subtree to physical live-frame
sums. Ancestor ownership is a current-state separation premise; constructing
the reachable whole live list remains a global proof obligation. -/
theorem normal_sums (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used requested : BitVec 64) (words : U256Zero.Quad) (ancestors : List (BitVec 64))
    (apart : FrameSums.Outside frame ancestors)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mcg : source.locals.lookup (ofString "mcg") = some (CallGas.pair (CallGas.capped requested left)
      (CallGas.capped requested left + CallGas.stipend words)))
    (gasCell : source.memory (frame + 64#64) = .word left) (usedCell : source.memory (frame + 184#64) = .word used)
    (code : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216) (funded : CallGas.stipend words ≤ used)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (program continuation) = (some (.returned value), post)) :
    ∃ ready, 1 ≤ source.clock ∧ ready = {source with memory := ready.memory, clock := source.clock - 1} ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), post) ∧
      FrameSums.budget ready.memory (frame :: ancestors) + (CallGas.capped requested left + CallGas.stipend words).toNat = FrameSums.budget source.memory (frame :: ancestors) ∧
      FrameSums.used ready.memory (frame :: ancestors) + (CallGas.stipend words).toNat = FrameSums.used source.memory (frame :: ancestors) ∧
      (∀ earlier : Memory, ∀ credit : Nat,
        FrameSums.used earlier (frame :: ancestors) + credit ≤ FrameSums.used source.memory (frame :: ancestors) →
        (CallGas.stipend words).toNat < credit →
        FrameSums.used earlier (frame :: ancestors) + 1 ≤ FrameSums.used ready.memory (frame :: ancestors)) := by
  obtain ⟨ready, positive, canonical, restRun, ledger, usedReady, gasReady, usedDebit, footprint⟩ :=
    normal source post frame left used requested words ev mcg gasCell usedCell code cap funded continuation value run
  obtain ⟨ancestorBudget, ancestorUsed⟩ := FrameSums.outside_preserved source.memory ready.memory frame ancestors apart footprint
  have totalBudget : FrameSums.budget ready.memory (frame :: ancestors) + (CallGas.capped requested left + CallGas.stipend words).toNat = FrameSums.budget source.memory (frame :: ancestors) := by
    change regularBudget ready.memory frame + FrameSums.budget ready.memory ancestors + _ = regularBudget source.memory frame + FrameSums.budget source.memory ancestors
    rw [ancestorBudget]
    omega
  have totalUsed : FrameSums.used ready.memory (frame :: ancestors) + (CallGas.stipend words).toNat = FrameSums.used source.memory (frame :: ancestors) := by
    change (wordAt ready.memory (frame + 184#64)).toNat + FrameSums.used ready.memory ancestors + _ = (wordAt source.memory (frame + 184#64)).toNat + FrameSums.used source.memory ancestors
    have sourceUsed : (wordAt source.memory (frame + 184#64)).toNat = used.toNat := by
      simp only [wordAt, usedCell, WitnessRadix.MemoryBytes.wordBits]
    rw [ancestorUsed, sourceUsed]
    omega
  refine ⟨ready, positive, canonical, restRun, totalBudget, totalUsed, ?_⟩
  intro earlier credit credited surplus
  omega

end InitECandidate.Solver.GasBudget.ForwardPrefix

#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.normal_sums
