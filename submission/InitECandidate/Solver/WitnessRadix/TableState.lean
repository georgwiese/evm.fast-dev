import InitECandidate.Solver.WitnessRadix.TableExecution

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def beforeWrites (plan : AllocatedLayout.Plan) : List (BitVec 64 × BitVec 64) :=
  let table := BitVec.ofNat 64 plan.table
  [(table, 32#64), (table + 8#64, 32#64), (table + 16#64, BitVec.ofNat 64 plan.capacity),
   (table + 24#64, 0#64), (table + 32#64, BitVec.ofNat 64 (plan.table + 72)),
   (table + 40#64, BitVec.ofNat 64 (plan.table + 72 + 32 * plan.capacity))]
def afterWrites (plan : AllocatedLayout.Plan) : List (BitVec 64 × BitVec 64) :=
  let table := BitVec.ofNat 64 plan.table
  [(table + 48#64, usedAddress plan),
   (table + 56#64, BitVec.ofNat 64 (plan.table + 72 + 41 * plan.capacity + plan.padding)),
   (table + 64#64, BitVec.ofNat 64 (plan.table + 72 + 49 * plan.capacity + plan.padding))]
def resultMemory (memory : WordWrites.Memory) (be : Bool) (plan : AllocatedLayout.Plan) : WordWrites.Memory :=
  WordWrites.write (clearMemory (WordWrites.write memory (beforeWrites plan)) be plan) (afterWrites plan)

theorem entered_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) :
    (enteredState source plan).memory = resultMemory source.memory source.be plan := rfl

theorem entered_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) :
    (enteredState source plan).clock = source.clock - price plan.capacity := by
  change source.clock - 1 - 1 - 1 - 1 - clearCost plan.capacity - 1 - 1 = source.clock - (clearCost plan.capacity + 6)
  omega

theorem update_twice (map : HolFiniteMapExact MlS (ValueHOL 64)) (name : MlS) (first last : ValueHOL 64) :
    (map.update (name, first)).update (name, last) = map.update (name, last) := by
  apply HolFiniteMapExact.ext
  funext query
  by_cases same : name = query <;> simp [HolFiniteMapExact.update, FUPDATE, same]

/-- Exact whole table-constructor nonlocal state, including heap cursor,
all nine header stores, used clearing and the total source-clock payment. -/
theorem entered_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan) :
    emptyLocalsHOLFinite (enteredState source plan) = emptyLocalsHOLFinite { source with
      globals := source.globals.update (ofString "heap_ptr",
        .val (.word (BitVec.ofNat 64 (plan.table + 72 + 57 * plan.capacity + plan.padding))))
      memory := resultMemory source.memory source.be plan
      clock := source.clock - price plan.capacity } := by
  have memory := entered_memory source plan
  have clock := entered_clock source plan
  rw [show emptyLocalsHOLFinite (enteredState source plan) = emptyLocalsHOLFinite
    { enteredState source plan with
      memory := resultMemory source.memory source.be plan
      clock := source.clock - price plan.capacity } by rw [← memory, ← clock]]
  simp only [enteredState, finishState, backupState, orderStored, orderState, usedStored, clearState,
    preClearState, valsStored, valsState, keysStored, keysState, initialState, headerState,
    PersistentAlloc.nextState, QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite, update_twice]

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.entered_memory
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.entered_clock
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.entered_frame
