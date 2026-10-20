import InitECandidate.Solver.Input.LittleEndianWriters
import InitECandidate.Solver.Input.BufferGlobals
import InitECandidate.Solver.Input.ByteStoreClock

namespace InitECandidate.Solver.Input.MemoryWordCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem le32_cost (code) : ClockCost.Bound code le32Body 0 := by
  rw [le32_shape]
  simp only [leClauses,GasBudget.Be32Stores.stores]
  repeat first
    | apply ClockCost.sequence code _ _ 0 0
    | exact ClockCost.store_byte code _ _
    | exact ClockCost.returned code _

theorem le32_globals (key : MlS) (code) : GlobalEffects.Preserves key code le32Body := by
  rw [le32_shape]
  simp only [leClauses,GasBudget.Be32Stores.stores]
  repeat first
    | apply GlobalEffects.sequence
    | exact GlobalEffects.store_byte key code _ _
    | exact GlobalEffects.returned key code _

theorem le64_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code le64Body 2 := by
  rw [le64_shape]
  unfold le64Tail
  exact ClockCost.sequence code _ _ 1 1
    (ClockCost.call_body code (some none) (ofString "st_le32") le64FirstArgs formals le32Body .one 0 (le32_code code installed) (le32_cost code))
    (ClockCost.sequence code _ _ 1 0
      (ClockCost.call_body code (some none) (ofString "st_le32") le64SecondArgs formals le32Body .one 0 (le32_code code installed) (le32_cost code)) (ClockCost.returned code _))

theorem le64_call_cost (code) (installed : OriginalCode.Installed code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "st_le64") arguments) 3 :=
  ClockCost.call_body code destination (ofString "st_le64") arguments formals le64Body .one 2 (le64_code code installed) (le64_cost code installed)

theorem le64_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code le64Body := by
  rw [le64_shape]
  unfold le64Tail
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "st_le32") le64FirstArgs formals le32Body .one (le32_code code installed) (le32_globals key code))
    (GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "st_le32") le64SecondArgs formals le32Body .one (le32_code code installed) (le32_globals key code)) (GlobalEffects.returned key code _))

end InitECandidate.Solver.Input.MemoryWordCalls

#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le32_cost
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le32_globals
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le64_cost
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le64_call_cost
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le64_globals
