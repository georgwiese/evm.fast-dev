import InitECandidate.Solver.GasBudget.RequireNotStatic

namespace InitECandidate.Solver.GasBudget.RequireNotStatic
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def call : ProgHOL 64 := .call (some (none, none)) (ofString "require_not_static") []
def program (continuation : ProgHOL 64) : ProgHOL 64 := .seq call continuation

theorem normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (continuation : ProgHOL 64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (program continuation) = (some (.returned value), post)) :
    1 ≤ source.clock ∧ evaluateHOLFiniteState {source with clock := source.clock - 1} continuation = (some (.returned value), post) := by
  have safe : Input.LocalPrefix (ofString "setup") call := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨checked, firstRun, continuationRun, saved⟩ := safe.normal_continue source post continuation value normal
  obtain ⟨positive, checkedEq⟩ := call_normal source checked installed firstRun
  rw [checkedEq] at continuationRun
  exact ⟨positive, continuationRun⟩

theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (continuation : ProgHOL 64)
    (installed : Input.OriginalCode.Installed source.code) (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (program continuation) = (some (.exception identifier payload), post)) :
    (1 ≤ source.clock ∧ post.clock = source.clock - 1 ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 1}) ∨
    (1 ≤ source.clock ∧ evaluateHOLFiniteState {source with clock := source.clock - 1} continuation = (some (.exception identifier payload), post)) := by
  rw [program, evaluateHOLFiniteState_seq_line780] at run
  generalize called : evaluateHOLFiniteState source call = output at run
  obtain ⟨result, checked⟩ := output
  cases result with
  | none =>
      obtain ⟨positive, checkedEq⟩ := call_normal source checked installed called
      rw [checkedEq] at run
      exact Or.inr ⟨positive, run⟩
  | some result =>
      have actual : evaluateHOLFiniteState source call = (some (.exception identifier payload), post) := called.trans run
      exact Or.inl (call_exception source post installed identifier payload actual)

end InitECandidate.Solver.GasBudget.RequireNotStatic

#print axioms InitECandidate.Solver.GasBudget.RequireNotStatic.normal_prefix
#print axioms InitECandidate.Solver.GasBudget.RequireNotStatic.exception_prefix
