import InitECandidate.Solver.MutableTable.GrowRuntime.Clear
import InitECandidate.Solver.WitnessRadix.TableLocals

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

structure AmountLocals {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (capacity : Nat) : Prop where
  cap : source.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 capacity)))
  stride : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind))))

theorem AmountLocals.allocated {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (capacity : Nat)
    (locals : AmountLocals source kind capacity) (name : String) (pointer next : Nat)
    (notCap : ofString name ≠ ofString "ncap") (notStride : ofString name ≠ ofString "stride") :
    AmountLocals (PersistentAlloc.nextState source name pointer next) kind capacity :=
  ⟨(bind_lookup_other _ name "ncap" _ notCap).trans locals.cap, (bind_lookup_other _ name "stride" _ notStride).trans locals.stride⟩

theorem read_capacity {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (capacity : Nat)
    (locals : AmountLocals source kind capacity) : eval source (localVar "ncap") = some (.val (.word (BitVec.ofNat 64 capacity))) := by
  simp [eval, localVar, evalHOLExact, toExact, locals.cap]

theorem read_key_amount {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (capacity : Nat)
    (locals : AmountLocals source kind capacity) :
    eval source (Grow.times (localVar "ncap") (localVar "stride")) = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind * capacity)))) := by
  simp [eval, Grow.times, localVar, evalHOLExact, evalListHOLExact, toExact, locals.cap, locals.stride,
    valueIsWord, valueWord, panOpHOL, ← BitVec.ofNat_mul, Nat.mul_comm capacity (NaturalLayout.stride kind)]

theorem read_word_amount {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (capacity : Nat)
    (locals : AmountLocals source kind capacity) :
    eval source (Grow.times (localVar "ncap") (.const 8#64)) = some (.val (.word (BitVec.ofNat 64 (8 * capacity)))) := by
  simp [eval, Grow.times, localVar, evalHOLExact, evalListHOLExact, toExact, locals.cap,
    valueIsWord, valueWord, panOpHOL, ← BitVec.ofNat_mul, Nat.mul_comm capacity 8]

def keyState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState source "nkeys" start (start + stride kind * capacity)
def valueState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState (keyState source kind start capacity) "nvals" (start + stride kind * capacity) (start + stride kind * capacity + 8 * capacity)
def usedState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState (valueState source kind start capacity) "nused" (start + stride kind * capacity + 8 * capacity)
    (start + stride kind * capacity + 8 * capacity + rounded capacity)
def orderState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState (usedState source kind start capacity) "norder" (start + stride kind * capacity + 8 * capacity + rounded capacity)
    (start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity)
def allocatedState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :=
  PersistentAlloc.nextState (orderState source kind start capacity) "norder_pos" (start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity)
    (relocatedEnd kind start capacity)

def allocationActions : List Action := (Grow.actions.drop 7).take 5

/-- All five real growth allocations in their unchanged order, including
allocator rounding, actual cursor updates and declaration scopes. -/
theorem allocations_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (table start capacity : Nat)
    (valid : Valid kind (relocated kind table start capacity)) (locals : AmountLocals source kind capacity)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (enough : 5 ≤ source.clock) :
    ∃ restoreStack, Executes source allocationActions (allocatedState source kind start capacity) restoreStack := by
  have keyFits : start + stride kind * capacity ≤ 33806089496 := valid.upper .keys
  have valueFits : start + stride kind * capacity + 8 * capacity ≤ 33806089496 := valid.upper .values
  have usedFits : start + stride kind * capacity + 8 * capacity + rounded capacity ≤ 33806089496 := valid.upper .used
  have orderFits : start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity ≤ 33806089496 := valid.upper .order
  have positionFits : relocatedEnd kind start capacity ≤ 33806089496 := valid.upper .position
  have keyAligned : (start + stride kind * capacity) % 8 = 0 := valid.aligned .values
  have valueAligned : (start + stride kind * capacity + 8 * capacity) % 8 = 0 := valid.aligned .used
  have usedAligned : (start + stride kind * capacity + 8 * capacity + rounded capacity) % 8 = 0 := valid.aligned .order
  have orderAligned : (start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity) % 8 = 0 := valid.aligned .position
  have positionAligned : relocatedEnd kind start capacity % 8 = 0 := by
    dsimp only [relocatedEnd]
    omega
  have roundBounds := rounded_bounds capacity
  have localsKey := AmountLocals.allocated source kind capacity locals "nkeys" start (start + stride kind * capacity) (by decide) (by decide)
  have localsValue := AmountLocals.allocated (keyState source kind start capacity) kind capacity localsKey "nvals" (start + stride kind * capacity) (start + stride kind * capacity + 8 * capacity) (by decide) (by decide)
  have localsUsed := AmountLocals.allocated (valueState source kind start capacity) kind capacity localsValue "nused" (start + stride kind * capacity + 8 * capacity) (start + stride kind * capacity + 8 * capacity + rounded capacity) (by decide) (by decide)
  have localsOrder := AmountLocals.allocated (usedState source kind start capacity) kind capacity localsUsed "norder" (start + stride kind * capacity + 8 * capacity + rounded capacity) (start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity) (by decide) (by decide)
  refine ⟨(fun target => restore source "nkeys" (restore (keyState source kind start capacity) "nvals"
    (restore (valueState source kind start capacity) "nused" (restore (usedState source kind start capacity) "norder"
      (restore (orderState source kind start capacity) "norder_pos" target))))), ?_⟩
  simp only [allocationActions, Grow.actions, List.drop, List.drop_zero, List.take, List.take_zero]
  apply PersistentAlloc.prefix_allocate source _ "nkeys" _ _ _ start (stride kind * capacity) (start + stride kind * capacity)
    (read_key_amount source kind capacity locals) code heap keyFits (Nat.le_refl _) (by omega) keyAligned (by omega)
  apply PersistentAlloc.prefix_allocate (keyState source kind start capacity) _ "nvals" _ _ _ (start + stride kind * capacity) (8 * capacity) (start + stride kind * capacity + 8 * capacity)
    (read_word_amount _ kind capacity localsKey) code (TableNew.allocated_heap source "nkeys" start (start + stride kind * capacity)) valueFits (Nat.le_refl _) (by omega) valueAligned (by change 1 ≤ source.clock - 1; omega)
  apply PersistentAlloc.prefix_allocate (valueState source kind start capacity) _ "nused" _ _ _ (start + stride kind * capacity + 8 * capacity) capacity (start + stride kind * capacity + 8 * capacity + rounded capacity)
    (read_capacity _ kind capacity localsValue) code (TableNew.allocated_heap (keyState source kind start capacity) "nvals" (start + stride kind * capacity) (start + stride kind * capacity + 8 * capacity))
    (by omega) (by omega) (by omega) usedAligned (by change 1 ≤ source.clock - 1 - 1; omega)
  apply PersistentAlloc.prefix_allocate (usedState source kind start capacity) _ "norder" _ _ _ (start + stride kind * capacity + 8 * capacity + rounded capacity) (8 * capacity) (start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity)
    (read_word_amount _ kind capacity localsUsed) code (TableNew.allocated_heap (valueState source kind start capacity) "nused" (start + stride kind * capacity + 8 * capacity) (start + stride kind * capacity + 8 * capacity + rounded capacity))
    orderFits (Nat.le_refl _) (by omega) orderAligned (by change 1 ≤ source.clock - 1 - 1 - 1; omega)
  apply PersistentAlloc.prefix_allocate (orderState source kind start capacity) _ "norder_pos" _ [] id (start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity) (8 * capacity) (relocatedEnd kind start capacity)
    (read_word_amount _ kind capacity localsOrder) code (TableNew.allocated_heap (usedState source kind start capacity) "norder" (start + stride kind * capacity + 8 * capacity + rounded capacity) (start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity))
    positionFits (Nat.le_refl _) (by dsimp only [relocatedEnd]; omega) positionAligned (by change 1 ≤ source.clock - 1 - 1 - 1 - 1; omega)
  exact .done _

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.AmountLocals.allocated
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.read_key_amount
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.read_word_amount
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.allocations_execute

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.read_capacity
