import InitECandidate.Solver.Headers.Slots

namespace InitECandidate.Solver.Headers
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def Slot.text : Slot→String | .f=>"f" | .d=>"d" | .w=>"w" | .tsf=>"tsf" | .ex=>"ex" | .bg=>"bg"
theorem Slot.of_text (slot : Slot) : ofString slot.text=slot.name := by cases slot <;> rfl
theorem Slot.not_array (slot : Slot) : slot.name≠ofString "arr" := by cases slot <;> decide
theorem Slot.not_header (slot : Slot) : slot.name≠ofString "h" := by cases slot <;> decide
theorem Slot.not_current (slot : Slot) : slot.name≠ofString "is_current" := by cases slot <;> decide

theorem Slots.tail (source : Flapjack.PanSemStateFiniteExact 64 Guest.HostMemory) (slot : Slot) (active : List Slot)
    (slots : Slots source (slot::active)) : Slots source active :=
  fun chosen member=>slots chosen (List.mem_cons_of_mem slot member)

end InitECandidate.Solver.Headers
