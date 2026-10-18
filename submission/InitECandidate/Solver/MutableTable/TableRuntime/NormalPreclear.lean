import InitECandidate.Solver.MutableTable.TableRuntime.NormalHeader
import InitECandidate.Solver.WitnessRadix.TableLocals

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def afterUsed : ProgHOL 64 := program (TableNew.actions.drop 11) TableNew.returnTable

theorem singleton_args (source : PanSemStateFiniteExact 64 Guest.HostMemory) (expression : ExpHOL 64) (amount : Nat)
    (read : eval source expression = some (.val (.word (BitVec.ofNat 64 amount)))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [expression] = some (PersistentAlloc.values (BitVec.ofNat 64 amount)) := by
  simp only [eval] at read
  simp [evalListHOLFinite, evalListHOLExact, read, PersistentAlloc.values]

/-- Derive room for the three real pre-clear allocations from their reached
normal calls. Header stores retain locals/cursor without assuming mappings. -/
theorem normal_preclear (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (locals : Locals source kind (BitVec.ofNat 64 start) capacity) (headerBound : start + 72 ≤ 33806089496) (startAligned : start % 8 = 0)
    (keySmall : stride kind * capacity < 2 ^ 64) (wordSmall : 8 * capacity < 2 ^ 64) (capSmall : capacity < 2 ^ 64)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 72)))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterHeader = (some (.returned value), target)) :
    start + 72 + stride kind * capacity + 8 * capacity + rounded capacity ≤ 33806089496 ∧
    ∃ reached inner : PanSemStateFiniteExact 64 Guest.HostMemory, evaluateHOLFiniteState reached afterUsed = (some (.returned value), inner) ∧
      Locals reached kind (BitVec.ofNat 64 start) capacity ∧
      reached.locals.lookup (ofString "used") = some (.val (.word (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity)))) ∧
      reached.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)))) ∧
      reached.code = source.code ∧ reached.memaddrs = source.memaddrs ∧ reached.be = source.be := by
  let keyEnd := start + 72 + stride kind * capacity
  let valueEnd := keyEnd + 8 * capacity
  let usedEnd := valueEnd + rounded capacity
  have strideAligned := (stride_bounds kind).2.2
  have roundedBounds := rounded_bounds capacity
  have keyAligned : keyEnd % 8 = 0 := by simp [keyEnd, Nat.add_mod, Nat.mul_mod, startAligned, strideAligned]
  have valueAligned : valueEnd % 8 = 0 := by simp [valueEnd, Nat.add_mod, Nat.mul_mod, keyAligned]
  have usedAligned : usedEnd % 8 = 0 := by simp [usedEnd, Nat.add_mod, valueAligned, roundedBounds.2.2]
  change evaluateHOLFiniteState source (.decCall (ofString "keys") .one (ofString "alloc") [TableNew.capacityTimes (localVar "stride")] _) = _ at normal
  obtain ⟨_, keyBound, _, keyTarget, keyRun, _⟩ := PersistentAlloc.call_normal_expected source target "keys" _ _ (start + 72) (stride kind * capacity) keyEnd
    headerBound keySmall (Nat.le_refl _) (by dsimp only [keyEnd]; omega) keyAligned
    (singleton_args source _ _ (read_key_amount source kind _ capacity locals)) code trapCode heap value normal
  let allocatedKeys := PersistentAlloc.nextState source "keys" (start + 72) keyEnd
  obtain ⟨keyMemory, afterKey⟩ := Input.store_normal_continue allocatedKeys keyTarget _ _ _ value keyRun
  let keys := {allocatedKeys with memory := keyMemory}
  have allocatedKeyLocals := Locals.allocated source kind _ capacity locals "keys" (start + 72) keyEnd (by decide) (by decide) (by decide)
  have keysLocals : Locals keys kind (BitVec.ofNat 64 start) capacity := ⟨allocatedKeyLocals.tableLocal, allocatedKeyLocals.capLocal, allocatedKeyLocals.strideLocal⟩
  obtain ⟨_, valueBound, _, valueTarget, valueRun, _⟩ := PersistentAlloc.call_normal_expected keys keyTarget "vals" _ _ keyEnd (8 * capacity) valueEnd
    keyBound wordSmall (Nat.le_refl _) (by dsimp only [valueEnd]; omega) valueAligned
    (singleton_args keys _ _ (read_scale keys kind _ capacity 8 keysLocals)) code trapCode
    (TableNew.allocated_heap source "keys" (start + 72) keyEnd) value afterKey
  let allocatedValues := PersistentAlloc.nextState keys "vals" keyEnd valueEnd
  obtain ⟨valueMemory, afterValue⟩ := Input.store_normal_continue allocatedValues valueTarget _ _ _ value valueRun
  let values := {allocatedValues with memory := valueMemory}
  have allocatedValueLocals := Locals.allocated keys kind _ capacity keysLocals "vals" keyEnd valueEnd (by decide) (by decide) (by decide)
  have valueLocals : Locals values kind (BitVec.ofNat 64 start) capacity := ⟨allocatedValueLocals.tableLocal, allocatedValueLocals.capLocal, allocatedValueLocals.strideLocal⟩
  obtain ⟨_, usedBound, _, usedTarget, usedRun, _⟩ := PersistentAlloc.call_normal_expected values valueTarget "used" _ _ valueEnd capacity usedEnd
    valueBound capSmall (by dsimp only [usedEnd]; omega) (by dsimp only [usedEnd]; omega) usedAligned
    (singleton_args values _ _ (read_capacity values kind _ capacity valueLocals)) code trapCode
    (TableNew.allocated_heap keys "vals" keyEnd valueEnd) value afterValue
  let reached := PersistentAlloc.nextState values "used" valueEnd usedEnd
  refine ⟨usedBound, reached, usedTarget, usedRun, Locals.allocated values kind _ capacity valueLocals "used" _ _ (by decide) (by decide) (by decide),
    bind_lookup_same _ _ _, TableNew.allocated_heap values "used" valueEnd usedEnd, rfl, rfl, rfl⟩

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.singleton_args
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.normal_preclear
