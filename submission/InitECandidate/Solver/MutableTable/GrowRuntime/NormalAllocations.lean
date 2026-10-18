import InitECandidate.Solver.MutableTable.GrowRuntime.Allocations
import InitECandidate.Solver.WitnessRadix.AllocationNormalExpected

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

private theorem singleton_args (source : PanSemStateFiniteExact 64 Guest.HostMemory) (expression : ExpHOL 64) (amount : Nat)
    (read : eval source expression = some (.val (.word (BitVec.ofNat 64 amount)))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [expression] = some (PersistentAlloc.values (BitVec.ofNat 64 amount)) := by
  simp only [eval] at read
  simp [evalListHOLFinite, evalListHOLExact, read, PersistentAlloc.values]

/-- Actual normal completion through all five original growth allocations
derives their combined exact reservation bound. No prospective new-layout
validity or heap-room premise is assumed. -/
theorem allocations_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (locals : AmountLocals source kind capacity) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (keySmall : stride kind * capacity < 2 ^ 64) (wordSmall : 8 * capacity < 2 ^ 64) (capSmall : capacity < 2 ^ 64)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (program allocationActions continuation) = (some (.returned value), target)) :
    relocatedEnd kind start capacity ≤ 33806089496 := by
  let keyEnd := start + stride kind * capacity
  let valueEnd := keyEnd + 8 * capacity
  let usedEnd := valueEnd + rounded capacity
  let orderEnd := usedEnd + 8 * capacity
  have strideAligned := (stride_bounds kind).2.2
  have roundedBounds := rounded_bounds capacity
  have keyAligned : keyEnd % 8 = 0 := by simp [keyEnd, Nat.add_mod, Nat.mul_mod, startAligned, strideAligned]
  have valueAligned : valueEnd % 8 = 0 := by simp [valueEnd, Nat.add_mod, Nat.mul_mod, keyAligned]
  have usedAligned : usedEnd % 8 = 0 := by simp [usedEnd, Nat.add_mod, valueAligned, roundedBounds.2.2]
  have orderAligned : orderEnd % 8 = 0 := by simp [orderEnd, Nat.add_mod, Nat.mul_mod, usedAligned]
  have finalAligned : relocatedEnd kind start capacity % 8 = 0 := by
    change (orderEnd + 8 * capacity) % 8 = 0
    simp [Nat.add_mod, Nat.mul_mod, orderAligned]
  have localsKey := AmountLocals.allocated source kind capacity locals "nkeys" start keyEnd (by decide) (by decide)
  have localsValue := AmountLocals.allocated (keyState source kind start capacity) kind capacity localsKey "nvals" keyEnd valueEnd (by decide) (by decide)
  have localsUsed := AmountLocals.allocated (valueState source kind start capacity) kind capacity localsValue "nused" valueEnd usedEnd (by decide) (by decide)
  have localsOrder := AmountLocals.allocated (usedState source kind start capacity) kind capacity localsUsed "norder" usedEnd orderEnd (by decide) (by decide)
  simp only [allocationActions, Grow.actions, List.drop, List.drop_zero, List.take, List.take_zero, program] at normal
  obtain ⟨_, keyBound, _, keyTarget, keyRun, _⟩ := PersistentAlloc.call_normal_expected source target "nkeys" _ _ start (stride kind * capacity) keyEnd
    startBound keySmall (Nat.le_refl _) (by dsimp only [keyEnd]; omega) keyAligned
    (singleton_args source _ _ (read_key_amount source kind capacity locals)) code trapCode heap value normal
  obtain ⟨_, valueBound, _, valueTarget, valueRun, _⟩ := PersistentAlloc.call_normal_expected (keyState source kind start capacity) keyTarget "nvals" _ _ keyEnd (8 * capacity) valueEnd
    keyBound wordSmall (Nat.le_refl _) (by dsimp only [valueEnd]; omega) valueAligned
    (singleton_args _ _ _ (read_word_amount _ kind capacity localsKey)) code trapCode
    (TableNew.allocated_heap source "nkeys" start keyEnd) value keyRun
  obtain ⟨_, usedBound, _, usedTarget, usedRun, _⟩ := PersistentAlloc.call_normal_expected (valueState source kind start capacity) valueTarget "nused" _ _ valueEnd capacity usedEnd
    valueBound capSmall (by dsimp only [usedEnd]; omega) (by dsimp only [usedEnd]; omega) usedAligned
    (singleton_args _ _ _ (read_capacity _ kind capacity localsValue)) code trapCode
    (TableNew.allocated_heap (keyState source kind start capacity) "nvals" keyEnd valueEnd) value valueRun
  obtain ⟨_, orderBound, _, orderTarget, orderRun, _⟩ := PersistentAlloc.call_normal_expected (usedState source kind start capacity) usedTarget "norder" _ _ usedEnd (8 * capacity) orderEnd
    usedBound wordSmall (Nat.le_refl _) (by dsimp only [orderEnd]; omega) orderAligned
    (singleton_args _ _ _ (read_word_amount _ kind capacity localsUsed)) code trapCode
    (TableNew.allocated_heap (valueState source kind start capacity) "nused" valueEnd usedEnd) value usedRun
  obtain ⟨_, finalBound, _, _, _, _⟩ := PersistentAlloc.call_normal_expected (orderState source kind start capacity) orderTarget "norder_pos" _ _ orderEnd (8 * capacity) (relocatedEnd kind start capacity)
    orderBound wordSmall (Nat.le_refl _) (by dsimp only [relocatedEnd, orderEnd, usedEnd, valueEnd, keyEnd]; omega) finalAligned
    (singleton_args _ _ _ (read_word_amount _ kind capacity localsOrder)) code trapCode
    (TableNew.allocated_heap (usedState source kind start capacity) "norder" usedEnd orderEnd) value orderRun
  exact finalBound

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.allocations_normal
