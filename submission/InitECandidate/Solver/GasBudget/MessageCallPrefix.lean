import InitECandidate.Solver.GasBudget.MessageCallProgram
import InitECandidate.Solver.MutableTable.ZeroRegion
import InitECandidate.Solver.MutableTable.MemoryModelBeforeFloor

namespace InitECandidate.Solver.GasBudget.MessageCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

def clearedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  bind {source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (cursor + 96))))
    memory := Zero.finalMemory source.memory (BitVec.ofNat 64 cursor) 96
    clock := source.clock - 5} "out" (BitVec.ofNat 64 cursor)

/-- The original message-call result allocation and whole96byte clear,
with reached room and exact source-clock payment derived from normal return. -/
theorem prefix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (environment : WarmKeys.Environment source) (lower : 2701131776 ≤ cursor)
    (bounded : cursor ≤ 33806089496) (aligned : cursor % 8 = 0)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    MemoryRegion.Valid ⟨cursor, 96⟩ ∧ 5 ≤ source.clock ∧ ∃ inner,
      evaluateHOLFiniteState (clearedState source cursor) afterZero = (some (.returned value), inner) ∧ post = restore source "out" inner := by
  rw [body_shape, StateSteps.next_sequence source source .skip _ (by rw [evaluateHOLFiniteState_skip]) (Nat.le_refl _)] at normal
  obtain ⟨_, room, positive, allocatedPost, allocatedRun, restored⟩ := PersistentAlloc.call_normal_expected source post "out" _ _ cursor 96 (cursor + 96)
    bounded (by decide) (Nat.le_refl _) (by omega) (by omega) rfl environment.allocCode environment.trapCode heap value normal
  let allocated := PersistentAlloc.nextState source "out" cursor (cursor + 96)
  have outLocal : allocated.locals.lookup (ofString "out") = some (.val (.word (BitVec.ofNat 64 cursor))) := bind_lookup_same _ _ _
  have safe : Input.LocalPrefix (ofString "msg") clear := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨cleared, clearRun, restRun, _⟩ := safe.normal_continue allocated allocatedPost afterZero value allocatedRun
  have args : evalListHOLFinite allocated (h := fun address => Classical.propDecidable (allocated.memaddrs address)) [localVar "out", .const 96#64] =
      some (Zero.values (BitVec.ofNat 64 cursor) 96) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, outLocal, Zero.values]
  have region : MemoryRegion.Valid ⟨cursor, 96⟩ := ⟨lower, room, aligned⟩
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have mapped : ∀ offset, offset + 8 ≤ 96 → offset % 8 = 0 → allocated.memaddrs (byteAddress (BitVec.ofNat 64 cursor) offset) := by
    intro offset inside offsetAligned
    rw [show allocated.memaddrs = source.memaddrs from rfl, environment.domain]
    exact MemoryRegion.word_mapped ⟨cursor, 96⟩ region offset inside offsetAligned
  obtain ⟨fits, same⟩ := Zero.call_normal allocated cleared _ (BitVec.ofNat 64 cursor) 96 args environment.zeroCode (by decide) (by decide) (by rw [number]; exact aligned) mapped clearRun
  have clearPrice : Zero.price 96 + 1 = 4 := by decide
  rw [clearPrice] at fits same
  have clock : source.clock - 1 - 4 = source.clock - 5 := by omega
  have clearedEq : cleared = clearedState source cursor := by
    rw [same]
    change bind {source with globals := _, clock := source.clock - 1 - 4, memory := _} "out" _ = _
    rw [clock]
    rfl
  rw [clearedEq] at restRun
  exact ⟨region, by change 4 ≤ source.clock - 1 at fits; omega, allocatedPost, restRun, restored⟩

theorem cleared_earlier (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (region : MemoryRegion.Valid ⟨cursor, 96⟩) (query : BitVec 64) (before : query.toNat < cursor) :
    (clearedState source cursor).memory query = source.memory query :=
  zero_region_outside source.memory ⟨cursor, 96⟩ region query (Or.inl before)

theorem cleared_table (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (region : MemoryRegion.Valid ⟨cursor, 96⟩) : TableState (clearedState source cursor) kind plan slots (cursor + 96) floor := by
  have allocated := table.after_alloc "out" (cursor + 96) (by omega) region.upper (by have aligned := table.aligned; omega)
  apply TableState.of_pool_frame (target := clearedState source cursor) allocated rfl rfl rfl
  exact MemoryModel.PoolFrame.of_protected_before source.memory (clearedState source cursor).memory kind plan table.valid cursor table.earlier
    (cleared_earlier source cursor region)

end InitECandidate.Solver.GasBudget.MessageCall

#print axioms InitECandidate.Solver.GasBudget.MessageCall.prefix_normal
#print axioms InitECandidate.Solver.GasBudget.MessageCall.cleared_earlier
#print axioms InitECandidate.Solver.GasBudget.MessageCall.cleared_table
