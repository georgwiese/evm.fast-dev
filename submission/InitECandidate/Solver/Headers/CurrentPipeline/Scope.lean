import InitECandidate.Solver.Headers.CurrentPipeline.State
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem State.drop_slot (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (slot : Slot) (active : List Slot)
    (state : State source pointer array header current bytes items (slot::active)) :
    State source pointer array header current bytes items active :=
  state.of_parts active state.slices (state.slots.tail source slot active) rfl state.arrayCell state.headerCell state.currentCell

/-- Lexical exit restores the saved binding, including an earlier binding
of the same slot. Other active local types and all physical data survive. -/
theorem State.restore (source inner : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (slot : Slot) (active : List Slot)
    (saved : State source pointer array header current bytes items active)
    (state : State inner pointer array header current bytes items (slot::active)) :
    State (WitnessRadix.QueryBranch.restore source slot.text inner) pointer array header current bytes items active := by
  let target:=WitnessRadix.QueryBranch.restore source slot.text inner
  have slices : CurrentHelpers.SliceImage target pointer array bytes items := state.slices.of_frame rfl
  have slots : Slots target active := by
    intro chosen member
    by_cases same : chosen=slot
    · subst chosen
      obtain ⟨value,cell,shape⟩ := saved.slots slot member
      refine ⟨value,?_,shape⟩
      change (HolFiniteMapExact.resVarEq inner.locals (ofString slot.text,source.locals.lookup (ofString slot.text))).lookup slot.name=some value
      rw [lookup_resVarEq_toExact,slot.of_text,cell]
      simp [resVarHOLExact,FUPDATE]
    · obtain ⟨value,cell,shape⟩ := state.slots chosen (List.mem_cons_of_mem slot member)
      have different : ofString chosen.text≠ofString slot.text := by
        rw [chosen.of_text,slot.of_text]
        intro equal
        exact same (Slot.name_injective equal)
      refine ⟨value,?_,shape⟩
      rw [←chosen.of_text,restore_lookup_other source inner slot.text chosen.text different,chosen.of_text]
      exact cell
  apply state.of_parts active slices slots rfl
  · exact (restore_lookup_other source inner slot.text "arr" (by rw [slot.of_text]; exact Ne.symm slot.not_array)).trans state.arrayCell
  · exact (restore_lookup_other source inner slot.text "h" (by rw [slot.of_text]; exact Ne.symm slot.not_header)).trans state.headerCell
  · exact (restore_lookup_other source inner slot.text "is_current" (by rw [slot.of_text]; exact Ne.symm slot.not_current)).trans state.currentCell

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.State.drop_slot
#print axioms InitECandidate.Solver.Headers.CurrentPipeline.State.restore
