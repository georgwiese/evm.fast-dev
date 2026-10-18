import InitECandidate.Solver.GasBudget.Calls
import InitECandidate.Solver.ClockPaddingFull

namespace InitECandidate.Solver.GasBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normal state refund derives its exact two call clocks and keeps
the capped regular ledger. No entry funding or non-wrap premise is needed. -/
theorem refund_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word amount)])
    (code : source.code.lookup (ofString "credit_state_gas_refund") = some (Refund.formals, Refund.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : ∀ offset ∈ ([64, 72, 192] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (gasCell : source.memory (frame + 64#64) = .word gas) (stateCell : source.memory (frame + 72#64) = .word state)
    (spillCell : source.memory (frame + 192#64) = .word spill)
    (minCode : source.code.lookup (ofString "min") = some (Minimum.formals, Minimum.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "credit_state_gas_refund") expressions) = (none, target)) :
    2 ≤ source.clock ∧ target.clock = source.clock - 2 ∧
      target = {source with memory := target.memory, clock := source.clock - 2} ∧ regularBudget target.memory frame = regularBudget source.memory frame := by
  classical
  have fits : gas.toNat + spill.toNat < 2 ^ 64 := by
    simp only [regularBudget, wordAt, gasCell, spillCell, WitnessRadix.MemoryBytes.wordBits] at cap
    omega
  let padded := {source with clock := source.clock + 2}
  have paddedArgs : evalListHOLFinite padded (h := fun address => Classical.propDecidable (padded.memaddrs address)) expressions = some [.val (.word amount)] := by
    change evalListHOLExact (stateAddClock source.toExact 2) expressions = _
    rw [evalListHOLExact_stateAddClock]
    exact args
  obtain ⟨memory, actual, budget⟩ := refund_call padded frame gas state spill amount expressions paddedArgs code ev mapped gasCell stateCell spillCell minCode fits (by change 2 ≤ source.clock + 2; omega)
  have lifted := panPropsEvaluateAddClockEq (.call (some (none, none)) (ofString "credit_state_gas_refund") expressions) source none target 2 ⟨normal, by intro impossible; cases impossible⟩
  have same := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + 2} = {source with memory := memory, clock := source.clock + 2 - 2} at same
  have stripped := InitECandidate.Solver.strip_full_clock_padding source target {source with memory := memory} 2 2 (by omega) same
  refine ⟨stripped.1, ?_, ?_, ?_⟩
  · rw [stripped.2]
  · rw [stripped.2]
  · rw [stripped.2]; exact budget

/-- The actual rollback refill similarly derives its single call clock.
Only owned message/frame mappings and their exact current words are inputs. -/
theorem refill_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame message gas spill reservoir : BitVec 64)
    (code : source.code.lookup (ofString "refill_frame_state_gas") = some ([], Refill.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : ∀ offset ∈ ([64, 72, 112, 192] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (messageCell : source.memory (frame + 112#64) = .word message)
    (gasCell : source.memory (frame + 64#64) = .word gas) (spillCell : source.memory (frame + 192#64) = .word spill)
    (reservoirMapped : source.memaddrs (message + 48#64)) (reservoirCell : source.memory (message + 48#64) = .word reservoir)
    (reservoirAway : message + 48#64 ≠ frame + 64#64)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "refill_frame_state_gas") []) = (none, target)) :
    1 ≤ source.clock ∧ target.clock = source.clock - 1 ∧
      target = {source with memory := target.memory, clock := source.clock - 1} ∧ regularBudget target.memory frame = regularBudget source.memory frame := by
  have fits : gas.toNat + spill.toNat < 2 ^ 64 := by
    simp only [regularBudget, wordAt, gasCell, spillCell, WitnessRadix.MemoryBytes.wordBits] at cap
    omega
  let padded := {source with clock := source.clock + 1}
  obtain ⟨memory, actual, budget⟩ := refill_call padded frame message gas spill reservoir code ev mapped messageCell gasCell spillCell reservoirMapped reservoirCell reservoirAway fits
    (by change 1 ≤ source.clock + 1; omega)
  have lifted := panPropsEvaluateAddClockEq (.call (some (none, none)) (ofString "refill_frame_state_gas") []) source none target 1 ⟨normal, by intro impossible; cases impossible⟩
  have same := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + 1} = {source with memory := memory, clock := source.clock + 1 - 1} at same
  have stripped := InitECandidate.Solver.strip_full_clock_padding source target {source with memory := memory} 1 1 (by omega) same
  refine ⟨stripped.1, ?_, ?_, ?_⟩
  · rw [stripped.2]
  · rw [stripped.2]
  · rw [stripped.2]; exact budget

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.refund_normal
#print axioms InitECandidate.Solver.GasBudget.refill_normal
