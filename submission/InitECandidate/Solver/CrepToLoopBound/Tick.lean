import InitECandidate.Solver.CrepToLoopBound.Common
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Leaf

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem simulateTick {width : Nat} [NeZero width] {σ : Type}
    (limit : Nat) (v1 : CrepSemHOLState width σ) : Simulation limit .tick v1 := by
  intro safe bounded res s1 t ctxt live hEval hNotError hState hMem hGlobals hCode hLocals
  have hClock : v1.clock = t.clock := hState.2.2.1
  by_cases hZero : v1.clock = 0
  · have hSource : (res, s1) =
        (some .timeOut, CrepSemHOLState.emptyLocals v1) := by
      simpa [evalCrepSemHOLProgExact_tick, hZero] using hEval.symm
    cases hSource
    have hTargetZero : t.clock = 0 := by omega
    refine ⟨0, some .timeOut, { t with locals := .ln }, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [LoopSemStateFiniteExact.evaluate, compileHOLExact, hTargetZero]
    · simpa [crepToLoopStateRelExact, CrepSemHOLState.emptyLocals,
        LoopSemStateFiniteExact.evaluate, hTargetZero] using hState
    · simpa [CrepSemHOLState.emptyLocals] using hMem
    · simpa [CrepSemHOLState.emptyLocals] using hGlobals
    · simpa [CrepSemHOLState.emptyLocals] using hCode
    · rfl
    · trivial
  · have hSource : (res, s1) = (none, decClockCrepSemHOL v1) := by
      simpa [evalCrepSemHOLProgExact_tick, hZero] using hEval.symm
    cases hSource
    have hTargetNonzero : t.clock ≠ 0 := by omega
    refine ⟨0, none, LoopSemStateFiniteExact.decClock t, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [LoopSemStateFiniteExact.evaluate, compileHOLExact, hTargetNonzero]
    · simpa [crepToLoopStateRelExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock, hClock] using hState
    · simpa [crepToLoopMemRelHOLExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock] using hMem
    · simpa [crepToLoopGlobalsRelHOLExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock] using hGlobals
    · simpa [crepToLoopCodeRelExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock] using hCode
    · rfl
    · exact hLocals

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.simulateTick
