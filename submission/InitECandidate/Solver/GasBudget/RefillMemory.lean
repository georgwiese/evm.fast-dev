import InitECandidate.Solver.GasBudget.RefundNormal
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.GasBudget.Refill
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Actual original refill caller: derive its one clock and exact three
word writes, including the complete outside-word memory frame. -/
theorem call_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame message gas spill reservoir : BitVec 64)
    (code : source.code.lookup (ofString "refill_frame_state_gas") = some ([], body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : ∀ offset ∈ ([64, 72, 112, 192] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (messageCell : source.memory (frame + 112#64) = .word message)
    (gasCell : source.memory (frame + 64#64) = .word gas) (spillCell : source.memory (frame + 192#64) = .word spill)
    (reservoirMapped : source.memaddrs (message + 48#64)) (reservoirCell : source.memory (message + 48#64) = .word reservoir)
    (reservoirAway : message + 48#64 ≠ frame + 64#64)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "refill_frame_state_gas") []) = (none, target)) :
    1 ≤ source.clock ∧ target = {source with memory := WordWrites.write source.memory (writes frame gas spill reservoir), clock := source.clock - 1} ∧
      (∀ address, address ≠ frame + 64#64 → address ≠ frame + 72#64 → address ≠ frame + 192#64 → target.memory address = source.memory address) := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "refill_frame_state_gas") [] = some (body, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup source.code.lookup _ [] body (fun _ => none) .one raw
  obtain ⟨positive, post, returned, actualRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "refill_frame_state_gas") [] [] body callee .one rfl called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨expected, bodyRun, memoryEq, fields⟩ := execute entry frame message gas spill reservoir ev mapped messageCell gasCell spillCell reservoirMapped reservoirCell reservoirAway
  have callerFrame : emptyLocalsHOLFinite expected = emptyLocalsHOLFinite {source with memory := expected.memory, clock := source.clock - 1} := fields
  have actual := ignored_return source expected (ofString "refill_frame_state_gas") [] [] body callee 1 rfl called positive bodyRun callerFrame
  have canonical := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := expected.memory, clock := source.clock - 1} at canonical
  change expected.memory = WordWrites.write source.memory (writes frame gas spill reservoir) at memoryEq
  rw [memoryEq] at canonical
  refine ⟨positive, canonical, ?_⟩
  intro address notGas notState notSpill
  rw [canonical]
  exact WordWrites.write_away source.memory _ address (by simp [writes, notGas, notState, notSpill])

end InitECandidate.Solver.GasBudget.Refill

#print axioms InitECandidate.Solver.GasBudget.Refill.call_memory
