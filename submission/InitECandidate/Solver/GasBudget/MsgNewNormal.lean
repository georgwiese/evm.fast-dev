import InitECandidate.Solver.GasBudget.MsgNewProgram

namespace InitECandidate.Solver.GasBudget.MsgNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable

theorem clear_price : Zero.price 176 + 1 = 8 := by decide

/-- Whole unchanged persistent message constructor on a genuine normal
return. Its reached allocator establishes all176bytes of message ownership;
the exact body price is9source clocks, derived without a funding premise. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat)
    (lower : 2701131776 ≤ start) (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), target)) :
    MemoryRegion.Valid ⟨start, 176⟩ ∧ 9 ≤ source.clock ∧ value = .val (.word (BitVec.ofNat 64 start)) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (start + 176))))
        memory := Zero.finalMemory source.memory (BitVec.ofNat 64 start) 176
        clock := source.clock - 9} := by
  rw [body_shape] at normal
  obtain ⟨_, room, positive, allocatedTarget, allocatedRun, restored⟩ := PersistentAlloc.call_normal_expected source target "m" _ _ start 176 (start + 176)
    bounded (by decide) (Nat.le_refl _) (by omega) (by omega) rfl allocCode trapCode heap value normal
  have region : MemoryRegion.Valid ⟨start, 176⟩ := ⟨lower, room, aligned⟩
  let allocated := PersistentAlloc.nextState source "m" start (start + 176)
  have messageLocal : allocated.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) := bind_lookup_same _ _ _
  have safe : Input.LocalPrefix (ofString "m") clearCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨cleared, clearRun, returnRun, _⟩ := safe.normal_continue allocated allocatedTarget returnMessage value allocatedRun
  have args : evalListHOLFinite allocated (h := fun address => Classical.propDecidable (allocated.memaddrs address)) [localVar "m", .const 176#64] = some (Zero.values (BitVec.ofNat 64 start) 176) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, messageLocal, Zero.values]
  have number : (BitVec.ofNat 64 start).toNat = start := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have mapped : ∀ offset, offset + 8 ≤ 176 → offset % 8 = 0 → allocated.memaddrs (byteAddress (BitVec.ofNat 64 start) offset) := by
    intro offset inside offsetAligned
    change source.memaddrs _
    rw [domain]
    exact MemoryRegion.word_mapped ⟨start, 176⟩ region offset inside offsetAligned
  obtain ⟨clearFits, clearedEq⟩ := Zero.call_normal allocated cleared _ (BitVec.ofNat 64 start) 176 args zeroCode (by decide) (by decide) (by rw [number]; exact aligned) mapped clearRun
  rw [clear_price] at clearFits clearedEq
  have actualReturn : evaluateHOLFiniteState cleared returnMessage = (some (.returned (.val (.word (BitVec.ofNat 64 start)))), emptyLocalsHOLFinite cleared) := by
    rw [clearedEq]
    simp [returnMessage, evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, messageLocal, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have valueEq := congrArg Prod.fst (returnRun.symm.trans actualReturn)
  have returned : value = .val (.word (BitVec.ofNat 64 start)) := by simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using valueEq
  have innerEq := congrArg Prod.snd (returnRun.symm.trans actualReturn)
  change allocatedTarget = emptyLocalsHOLFinite cleared at innerEq
  have frame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (start + 176))))
      memory := Zero.finalMemory source.memory (BitVec.ofNat 64 start) 176, clock := source.clock - 9} := by
    rw [restored, innerEq, clearedEq]
    change emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (start + 176))))
      memory := Zero.finalMemory source.memory (BitVec.ofNat 64 start) 176
      clock := source.clock - 1 - 8} = _
    have subtract : source.clock - 1 - 8 = source.clock - 9 := by omega
    rw [subtract]
  exact ⟨region, by change 8 ≤ source.clock - 1 at clearFits; omega, returned, frame⟩

end InitECandidate.Solver.GasBudget.MsgNew

#print axioms InitECandidate.Solver.GasBudget.MsgNew.clear_price
#print axioms InitECandidate.Solver.GasBudget.MsgNew.body_normal
