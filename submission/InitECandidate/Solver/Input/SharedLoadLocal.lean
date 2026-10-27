import InitECandidate.Solver.Input.LocalSummarySequence
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A shared read into another local preserves the tracked binding whenever
it continues. Missing mappings, malformed replies and terminal FFI remain
possible, but cannot escape as return, break or continue. -/
theorem shared_load_local {F : Type} (key name : MlS) (operator : OpSize)
    (expression : ExpHOL 64) (other : key ≠ name)
    (source : PanSemStateFiniteExact 64 F) :
    LocalSummary key (.shMemLoad operator .local name expression) source := by
  classical
  unfold LocalSummary
  rw [evaluateHOLFiniteState_shMemLoad_source]
  simp only [shMemLoadHOLFiniteExact]
  repeat' first
    | split
    | simp [setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite,
        HolFiniteMapExact.update, FUPDATE, Ne.symm other]

/-- Continuing shared reads do not advance another caller counter. -/
theorem CounterFlow.shared_load (key name : MlS) (operator : OpSize)
    (expression : ExpHOL 64) (other : key ≠ name) :
    Advances key 0 (.shMemLoad operator .local name expression) := by
  intro source post word cell run
  have summary := shared_load_local key name operator expression other source
  unfold LocalSummary at summary
  rw [run] at summary
  simpa only [BitVec.add_zero] using (summary.1 rfl).trans cell

/-- The actual continuing shared load installs a word in its destination.
This derives the observed scalar without promising any future readable byte. -/
theorem shared_load_normal_word {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (name : MlS) (operator : OpSize) (expression : ExpHOL 64)
    (normal : evaluateHOLFiniteState source (.shMemLoad operator .local name expression) = (none, target)) :
    ∃ word : BitVec 64, target.locals.lookup name = some (.val (.word word)) := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source] at normal
  simp only [shMemLoadHOLFiniteExact] at normal
  repeat' first
    | split at normal
    | cases normal
    | simp [setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite,
        HolFiniteMapExact.update, FUPDATE]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.shared_load_local
#print axioms InitECandidate.Solver.Input.CounterFlow.shared_load
#print axioms InitECandidate.Solver.Input.shared_load_normal_word
