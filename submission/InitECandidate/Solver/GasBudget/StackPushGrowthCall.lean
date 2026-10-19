import InitECandidate.Solver.GasBudget.StackPushGrowthBody
import InitECandidate.Solver.GasBudget.StackPushNonGrowthCall

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- The genuine stack_push caller derives argument shape, body funding,
growth and the resulting stack headers from its actual normal return. -/
theorem growth_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch memory capacity : BitVec 64)
    (view : GrowthView source frame base scratch memory capacity) (arguments : List (ExpHOL 64))
    (code : source.code.lookup (ofString "stack_push") = some (formals, body, .one))
    (copyApart : ∀ offset ∈ ([64, 184, 192] : List Nat),
      CopyGeneral.Away (growDestination scratch capacity) (frame + BitVec.ofNat 64 offset) (32 * capacity.toNat))
    (slotApart : ∀ offset ∈ ([8, 64, 184, 192, 232] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (growDestination scratch capacity + capacity * 32#64) + BitVec.ofNat 64 (8 * index))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "stack_push") arguments) = (none, target)) :
    capacity.toNat + 3 ≤ source.clock ∧ target.clock = source.clock - (capacity.toNat + 3) ∧
      target = {Arenas.post source .down scratch ((capacity * 2#64) * 32#64) with memory := target.memory, clock := source.clock - (capacity.toNat + 3)} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      target.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      target.memory (frame + 16#64) = .word (capacity + 1#64) ∧
      (wordAt target.memory (frame + 16#64)).toNat = capacity.toNat + 1 ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ (capacity * 2#64).toNat ∧
      target.memory (frame + 8#64) = .word (growDestination scratch capacity) ∧
      target.memory (frame + 232#64) = .word (capacity * 2#64) ∧
      (∀ address, address ≠ frame + 16#64 → address ≠ frame + 8#64 → address ≠ frame + 232#64 →
        CopyGeneral.Away (growDestination scratch capacity) address (32 * capacity.toNat) →
        (∀ index < 4, address ≠ (growDestination scratch capacity + capacity * 32#64) + BitVec.ofNat 64 (8 * index)) →
        target.memory address = source.memory address) := by
  obtain ⟨positive, values, actualBody, callee, returnShape, post, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source target (ofString "stack_push") arguments normal
  obtain ⟨storedValue, valuesEq, bodyEq, returnEq, valueShape, vLocal⟩ :=
    Input.CallNormal.unary_lookup_data source.code.lookup (ofString "stack_push") (ofString "v") (.comb [.one, .one, .one, .one]) body .one
      code values actualBody callee returnShape called
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have current : GrowthView entry frame base scratch memory capacity :=
    ⟨view.positive, view.bounded, view.ev, view.spCell, view.capCell, view.baseMapped, view.baseCell,
      view.scratchGlobal, view.memoryGlobal, view.arenaAligned, view.room, view.allocCode, view.copyCode,
      view.mapped.of_domain source entry _ _ _ rfl, view.aligned⟩
  obtain ⟨zero, funded, clock, frameEq, budget, used, spFinal, naturalSP, depth, baseFinal, capFinal, outside⟩ :=
    growth_body_normal entry post frame base scratch memory capacity current storedValue returned vLocal valueShape copyApart slotApart bodyRun
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frameEq
  have canonical : target = {Arenas.post source .down scratch ((capacity * 2#64) * 32#64) with memory := post.memory, clock := post.clock} :=
    postEq.trans callerFrame
  have total : post.clock = source.clock - (capacity.toNat + 3) := by
    rw [clock]
    change source.clock - 1 - (capacity.toNat + 2) = _
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change capacity.toNat + 2 ≤ source.clock - 1 at funded
    omega
  · rw [canonical]; exact total
  · rw [canonical, total]
  · rw [canonical]; exact budget
  · rw [canonical]; exact used
  · rw [canonical]; exact spFinal
  · rw [canonical]; exact naturalSP
  · rw [canonical]; exact depth
  · rw [canonical]; exact baseFinal
  · rw [canonical]; exact capFinal
  · intro address notSP notBase notCap away notSlot
    rw [canonical]
    exact outside address notSP notBase notCap away notSlot

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.growth_call_normal
