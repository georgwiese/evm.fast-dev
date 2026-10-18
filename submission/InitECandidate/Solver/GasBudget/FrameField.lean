import InitECandidate.Solver.GasBudget.Frame
import InitECandidate.Solver.Input.WordStoreNormal

namespace InitECandidate.Solver.GasBudget.FrameField
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- A real scalar frame-field store derives its actual destination mapping
and exact state effect. Caller globals/locals/code/clock remain available. -/
theorem normal_word (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame offset value : BitVec 64) (expression : ExpHOL 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (read : eval source expression = some (.val (.word value)))
    (normal : evaluateHOLFiniteState source (.store (frameAddress offset) expression) = (none, target)) :
    target = {source with memory := StoreWord.put source.memory (frame + offset) value} :=
  (Input.word_store_normal source target _ expression _ value (address_read source frame offset ev) read normal).2

theorem put_other (memory : Memory) (frame offset value field : BitVec 64) (different : field ≠ offset) :
    StoreWord.put memory (frame + offset) value (frame + field) = memory (frame + field) := by
  exact if_neg (offsets_ne frame field offset different)

theorem put_budget (memory : Memory) (frame offset value : BitVec 64)
    (notGas : (64#64 : BitVec 64) ≠ offset) (notUsed : (184#64 : BitVec 64) ≠ offset) (notSpill : (192#64 : BitVec 64) ≠ offset) :
    regularBudget (StoreWord.put memory (frame + offset) value) frame = regularBudget memory frame := by
  simp only [regularBudget, wordAt, put_other memory frame offset value 64#64 notGas,
    put_other memory frame offset value 184#64 notUsed, put_other memory frame offset value 192#64 notSpill]

/-- A distinct continuation-record store cannot alter the active gas ledger. -/
theorem put_budget_away (memory : Memory) (frame address value : BitVec 64)
    (away : ∀ offset ∈ ([64, 184, 192] : List Nat), frame + BitVec.ofNat 64 offset ≠ address) :
    regularBudget (StoreWord.put memory address value) frame = regularBudget memory frame := by
  simp only [regularBudget, wordAt, StoreWord.put,
    if_neg (away 64 (by simp)), if_neg (away 184 (by simp)), if_neg (away 192 (by simp))]

end InitECandidate.Solver.GasBudget.FrameField

#print axioms InitECandidate.Solver.GasBudget.FrameField.normal_word
#print axioms InitECandidate.Solver.GasBudget.FrameField.put_other
#print axioms InitECandidate.Solver.GasBudget.FrameField.put_budget
#print axioms InitECandidate.Solver.GasBudget.FrameField.put_budget_away
