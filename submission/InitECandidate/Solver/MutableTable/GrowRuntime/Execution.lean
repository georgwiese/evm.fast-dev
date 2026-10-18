import InitECandidate.Solver.MutableTable.GrowRuntime.Setup
import InitECandidate.Solver.MutableTable.GrowRuntime.Loop
import InitECandidate.Solver.MutableTable.GrowRuntime.Footprint

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def price (kind : KeyHash.Kind) (capacity count : Nat) := setupPrice capacity + loopPrice kind 0 count

/-- Complete original growth body. It doubles and relocates the arrays,
clears the new occupancy, reinserts every old dense-order item, returns and
restores all declaration scopes. The physical model and complete nonlocal
frame are derived from actual execution. Global heap reachability is still
an entry obligation, and these are source clocks rather than target steps. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (newValid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false) (multiple : (2 * old.capacity) % 8 = 0)
    (slots : List Nat) (room : slots.length ≤ old.capacity)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (bits : Nat) (small : bits < 64) (power : 2 * old.capacity = 2 ^ bits)
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (enough : price kind (2 * old.capacity) slots.length ≤ source.clock) :
    ∃ paid memory target next, paid ≤ price kind (2 * old.capacity) slots.length ∧
      evaluateHOLFiniteState source Grow.body = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (relocatedEnd kind start (2 * old.capacity)))))
        memory := memory, clock := source.clock - paid} ∧
      next.length = slots.length ∧
      MemoryModel.Header memory kind (relocated kind (old.base .header) start (2 * old.capacity)) (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind (relocated kind (old.base .header) start (2 * old.capacity)) next ∧ OldArrays target source kind old ∧
      TableFootprint.Frame source.memory memory kind (relocated kind (old.base .header) start (2 * old.capacity)) := by
  let plan := relocated kind (old.base .header) start (2 * old.capacity)
  let prepared := preparedState source kind old start slots.length
  have newRoom : slots.length < 2 * old.capacity := by have positive := oldValid.positive; omega
  have preparedModel := prepared_model source kind old start slots.length newValid multiple domain little
  have preparedHeader := prepared_header source kind old start slots.length newValid header
  have preparedOld := prepared_old_arrays source kind old oldValid start slots.length newValid earlier
  have preparedLocals := prepared_locals source kind old start slots.length tableLocal
  have loopEnough : loopPrice kind 0 slots.length ≤ prepared.clock := by
    rw [prepared_clock]
    dsimp only [price] at enough
    omega
  obtain ⟨paid, memory, target, next, bounded, run, frame, length, nextHeader, nextModel, nextOld, loopFootprint⟩ :=
    loop_execute source kind old oldValid start (2 * old.capacity) newValid earlier slots room newRoom occupied bits small power prepared domain little
      0 slots.length (Nat.zero_add _) preparedLocals [] rfl preparedHeader preparedModel preparedOld hashCode copyCode insertCode loopEnough
  have clock : target.clock = prepared.clock - paid := congrArg PanSemStateFiniteExact.clock frame
  have returnRun : evaluateHOLFiniteState target Grow.returnZero = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite target) := by
    simp [Grow.returnZero, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have tailRun : evaluateHOLFiniteState prepared (.seq Grow.loop Grow.returnZero) = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite target) := by
    rw [StateSteps.next_sequence prepared target Grow.loop Grow.returnZero run (by rw [clock]; omega), returnRun]
  obtain ⟨restoreStack, restoreFrame, setupRun⟩ := setup_execute source kind old oldValid start slots.length newValid domain multiple header tableLocal heap allocCode zeroCode
    (by dsimp only [price] at enough; omega)
  rw [tailRun] at setupRun
  have subtract : prepared.clock - paid = source.clock - (setupPrice (2 * old.capacity) + paid) := by
    rw [prepared_clock]
    omega
  have canonical : emptyLocalsHOLFinite {prepared with memory := memory, clock := prepared.clock - paid} =
      emptyLocalsHOLFinite {source with
        globals := (source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (relocatedEnd kind start (2 * old.capacity))))))
        memory := memory
        clock := source.clock - (setupPrice (2 * old.capacity) + paid)} := by
    rw [subtract]
    have actual := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := memory, clock := source.clock - (setupPrice (2 * old.capacity) + paid)})
      (prepared_frame source kind old start slots.length)
    exact actual
  have restoredMemory : target.memory = (restoreStack (emptyLocalsHOLFinite target)).memory := (congrArg PanSemStateFiniteExact.memory (restoreFrame (emptyLocalsHOLFinite target))).symm
  have restoredDomain : target.memaddrs = (restoreStack (emptyLocalsHOLFinite target)).memaddrs := (congrArg PanSemStateFiniteExact.memaddrs (restoreFrame (emptyLocalsHOLFinite target))).symm
  have restoredEndian : target.be = (restoreStack (emptyLocalsHOLFinite target)).be := (congrArg PanSemStateFiniteExact.be (restoreFrame (emptyLocalsHOLFinite target))).symm
  refine ⟨setupPrice (2 * old.capacity) + paid, memory, restoreStack (emptyLocalsHOLFinite target), next, ?_, setupRun, ?_, length, nextHeader, ?_, ?_, ?_⟩
  · dsimp only [price]
    omega
  · exact (restoreFrame (emptyLocalsHOLFinite target)).trans (frame.trans canonical)
  · exact MemoryModel.Occupied.of_fields target _ kind plan next nextModel restoredMemory restoredDomain restoredEndian
  · exact OldArrays.of_memory target _ source kind old restoredMemory nextOld
  · exact TableFootprint.Frame.trans source.memory prepared.memory memory kind plan (prepared_footprint source kind old start slots.length) loopFootprint

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.execute
