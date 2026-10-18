import InitECandidate.Solver.MutableTable.GrowRuntime.NormalAllocations
import InitECandidate.Solver.MutableTable.GrowRuntime.Setup
import InitECandidate.Solver.MutableTable.GrowRuntime.Environment

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

/-- Normal original growth reaches all five actual allocations. The old
physical extents derive no-wrap of their doubled natural amounts. -/
theorem normal_room (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (valid : Valid kind old) (start count : Nat) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 count))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Grow.body = (some (.returned value), target)) :
    relocatedEnd kind start (2 * old.capacity) ≤ 33806089496 := by
  let plan := relocated kind (old.base .header) start (2 * old.capacity)
  let rest : ProgHOL 64 := .seq clearCall (FieldStores.program "t" "" (resetFields plan) Grow.afterSetup)
  obtain ⟨restoreHeader, setup⟩ := header_execute source kind old valid domain count header tableLocal
  have actual := ProgramPrefix.execute setup (program allocationActions rest)
  have normalSetup := normal
  rw [setup_shape plan] at normalSetup
  have resultEq := congrArg Prod.fst (actual.symm.trans normalSetup)
  let entered := headerState source kind old count
  let allocationTarget := (evaluateHOLFiniteState entered (program allocationActions rest)).2
  have allocationRun : evaluateHOLFiniteState entered (program allocationActions rest) = (some (.returned value), allocationTarget) := Prod.ext resultEq rfl
  have keyUpper := valid.upper .keys
  have valueUpper := valid.upper .values
  change old.base .keys + stride kind * old.capacity ≤ 33806089496 at keyUpper
  change old.base .values + 8 * old.capacity ≤ 33806089496 at valueUpper
  have keySmall : stride kind * (2 * old.capacity) < 2 ^ 64 := by rw [Nat.mul_left_comm]; omega
  have wordSmall : 8 * (2 * old.capacity) < 2 ^ 64 := by rw [Nat.mul_left_comm]; omega
  have capSmall : 2 * old.capacity < 2 ^ 64 := by omega
  exact allocations_normal entered allocationTarget kind start (2 * old.capacity) (header_amount source kind old count)
    startBound startAligned keySmall wordSmall capSmall heap code trapCode rest value allocationRun

/-- Actual successful growth establishes the prospective layout's room;
it need not be demanded of an unexecuted growth branch. -/
theorem normal_layout (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (valid : Valid kind old) (start count : Nat) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 count))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Grow.body = (some (.returned value), target)) :
    Valid kind (relocated kind (old.base .header) start (2 * old.capacity)) := by
  have room := normal_room source target kind old valid start count startBound startAligned domain header tableLocal heap code trapCode value normal
  have before := earlier .header
  change old.base .header + 72 ≤ start at before
  exact relocated_valid kind (old.base .header) start (2 * old.capacity) (by have := valid.positive; omega)
    (valid.lower .header) (by have := valid.lower .header; omega) (valid.upper .header) room (valid.aligned .header) startAligned (Or.inl before)

theorem normal_call_layout (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (valid : Valid kind old) (start count : Nat) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start) (domain : source.memaddrs = InitE.ordinaryDomain)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 count))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (Grow.values (cell old .header 0)))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_grow") arguments) = (none, target)) :
    Valid kind (relocated kind (old.base .header) start (2 * old.capacity)) := by
  obtain ⟨callee, called, tableLocal⟩ := Grow.environment source.code.lookup (cell old .header 0) growCode
  obtain ⟨_, calleeTarget, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "htab_grow") arguments (Grow.values (cell old .header 0)) Grow.body callee .one args called normal
  exact normal_layout (callEntryStateHOLFinite source callee) calleeTarget kind old valid start count startBound startAligned earlier domain header tableLocal heap code trapCode returned bodyRun

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.normal_room
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.normal_layout
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.normal_call_layout
