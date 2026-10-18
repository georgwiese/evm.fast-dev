import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Any actual normal ordinary store changes memory alone. Evaluation and
mapping success follow from that outcome, with no supplied read oracle. -/
theorem store_none_frame {F : Type} (source target : PanSemStateFiniteExact 64 F) (address value : ExpHOL 64)
    (normal : evaluateHOLFiniteState source (.store address value) = (none, target)) :
    target = {source with memory := target.memory} := by
  classical
  rw [evaluateHOLFiniteState_store] at normal
  split at normal
  · split at normal
    · split at normal
      · have same := congrArg Prod.snd normal
        change {source with memory := _} = target at same
        rw [← same]
      · cases normal
    · cases normal
  · cases normal

/-- Reach an actual continuation after a store and expose only its memory
change. This is useful before later allocations establish the full layout. -/
theorem store_normal_continue {F : Type} (source post : PanSemStateFiniteExact 64 F) (address stored : ExpHOL 64)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (.store address stored) continuation) = (some (.returned value), post)) :
    ∃ memory, evaluateHOLFiniteState {source with memory := memory} continuation = (some (.returned value), post) := by
  obtain ⟨middle, run, rest, _⟩ := (LocalPrefix.store (key := ofString "cap") address stored).normal_continue source post continuation value normal
  have same := store_none_frame source middle address stored run
  rw [same] at rest
  exact ⟨middle.memory, rest⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.store_none_frame
#print axioms InitECandidate.Solver.Input.store_normal_continue
