import InitECandidate.Solver.MutableTable.TableRuntime.NormalPreclear
import InitECandidate.Solver.MutableTable.MemoryRegion
import InitECandidate.Solver.WitnessRadix.ZeroNormal

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

/-- The reached used buffer maps every real word written by memzero. -/
theorem used_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (lower : 2701131776 ≤ start) (aligned : start % 8 = 0)
    (usedBound : start + 72 + stride kind * capacity + 8 * capacity + rounded capacity ≤ 33806089496)
    (domain : source.memaddrs = InitE.ordinaryDomain) :
    ∀ offset, offset + 8 ≤ capacity → offset % 8 = 0 →
      source.memaddrs (byteAddress (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity)) offset) := by
  intro offset inside offsetAligned
  have roundBound := (rounded_bounds capacity).1
  have strideAligned := (stride_bounds kind).2.2
  rw [domain]
  have number : (byteAddress (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity)) offset).toNat =
      start + 72 + stride kind * capacity + 8 * capacity + offset := by
    rw [byteAddress, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply BackingLayout.ordinary_mapped
  · rw [number]; omega
  · rw [number]; omega
  · rw [number]
    simp [Nat.add_mod, Nat.mul_mod, aligned, strideAligned, offsetAligned]

/-- Normal execution of the real clear and both remaining allocations
derives the end of the complete fresh reservation. Only already-reached
used-buffer room is supplied; no prospective final layout is assumed. -/
theorem normal_finish (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (locals : Locals source kind (BitVec.ofNat 64 start) capacity)
    (usedLocal : source.locals.lookup (ofString "used") = some (.val (.word (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity)))))
    (lower : 2701131776 ≤ start) (startAligned : start % 8 = 0)
    (usedBound : start + 72 + stride kind * capacity + 8 * capacity + rounded capacity ≤ 33806089496)
    (wordSmall : 8 * capacity < 2 ^ 64) (capSmall : capacity + 32 < 2 ^ 64) (multiple : capacity % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterUsed = (some (.returned value), target)) :
    freshEnd kind start capacity ≤ 33806089496 := by
  let usedBase := start + 72 + stride kind * capacity + 8 * capacity
  let usedEnd := usedBase + rounded capacity
  let orderEnd := usedEnd + 8 * capacity
  have strideAligned := (stride_bounds kind).2.2
  have roundedAligned := (rounded_bounds capacity).2.2
  have usedAligned : usedBase % 8 = 0 := by simp [usedBase, Nat.add_mod, Nat.mul_mod, startAligned, strideAligned]
  have orderAligned : orderEnd % 8 = 0 := by simp [orderEnd, usedEnd, Nat.add_mod, Nat.mul_mod, usedAligned, roundedAligned]
  have finalAligned : freshEnd kind start capacity % 8 = 0 := by
    change (orderEnd + 8 * capacity) % 8 = 0
    simp [Nat.add_mod, Nat.mul_mod, orderAligned]
  have queryNumber : (BitVec.ofNat 64 usedBase).toNat = usedBase := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [usedBase]; omega)]
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "used", localVar "cap"] =
      some (Zero.values (BitVec.ofNat 64 usedBase) capacity) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, usedLocal, locals.capLocal, Zero.values, usedBase]
  have clearSafe : Input.LocalPrefix (ofString "cap") (.call (some (none, none)) (ofString "memzero") [localVar "used", localVar "cap"]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨cleared, clearRun, afterClear, _⟩ := clearSafe.normal_continue source target _ value normal
  obtain ⟨_, clearedEq⟩ := Zero.call_normal source cleared _ (BitVec.ofNat 64 usedBase) capacity args zeroCode capSmall multiple
    (by rw [queryNumber]; exact usedAligned) (used_mapped source kind start capacity lower startAligned usedBound domain) clearRun
  rw [clearedEq] at afterClear
  let clearedState := {source with memory := Zero.finalMemory source.memory (BitVec.ofNat 64 usedBase) capacity, clock := source.clock - (Zero.price capacity + 1)}
  obtain ⟨usedMemory, afterUsedStore⟩ := Input.store_normal_continue clearedState target _ _ _ value afterClear
  let used := {clearedState with memory := usedMemory}
  have usedLocals : Locals used kind (BitVec.ofNat 64 start) capacity := ⟨locals.tableLocal, locals.capLocal, locals.strideLocal⟩
  obtain ⟨_, orderBound, _, orderTarget, orderRun, _⟩ := PersistentAlloc.call_normal_expected used target "order" _ _ usedEnd (8 * capacity) orderEnd
    usedBound wordSmall (Nat.le_refl _) (by dsimp only [orderEnd]; omega) orderAligned
    (singleton_args used _ _ (read_scale used kind _ capacity 8 usedLocals)) code trapCode heap value afterUsedStore
  let allocatedOrder := PersistentAlloc.nextState used "order" usedEnd orderEnd
  obtain ⟨orderMemory, afterOrderStore⟩ := Input.store_normal_continue allocatedOrder orderTarget _ _ _ value orderRun
  let order := {allocatedOrder with memory := orderMemory}
  have allocatedOrderLocals := Locals.allocated used kind _ capacity usedLocals "order" usedEnd orderEnd (by decide) (by decide) (by decide)
  have orderLocals : Locals order kind (BitVec.ofNat 64 start) capacity := ⟨allocatedOrderLocals.tableLocal, allocatedOrderLocals.capLocal, allocatedOrderLocals.strideLocal⟩
  obtain ⟨_, finalBound, _, _, _, _⟩ := PersistentAlloc.call_normal_expected order orderTarget "order_pos" _ _ orderEnd (8 * capacity) (freshEnd kind start capacity)
    orderBound wordSmall (Nat.le_refl _) (by dsimp only [freshEnd, orderEnd, usedEnd, usedBase]; omega) finalAligned
    (singleton_args order _ _ (read_scale order kind _ capacity 8 orderLocals)) code trapCode
    (TableNew.allocated_heap used "order" usedEnd orderEnd) value afterOrderStore
  exact finalBound

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.used_mapped
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.normal_finish
