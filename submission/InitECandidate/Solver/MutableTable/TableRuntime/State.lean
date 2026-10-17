import InitECandidate.Solver.MutableTable.TableRuntime.Execution
import InitECandidate.Solver.WitnessRadix.TableState

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open NaturalLayout

def beforeWrites (kind : KeyHash.Kind) (start capacity : Nat) : List (BitVec 64 × BitVec 64) :=
  let table := BitVec.ofNat 64 start
  [(table, BitVec.ofNat 64 (KeyHash.keySize kind)), (table + 8#64, BitVec.ofNat 64 (stride kind)),
   (table + 16#64, BitVec.ofNat 64 capacity), (table + 24#64, 0#64),
   (table + 32#64, BitVec.ofNat 64 (start + 72)), (table + 40#64, BitVec.ofNat 64 (start + 72 + stride kind * capacity))]
def afterWrites (kind : KeyHash.Kind) (start capacity : Nat) : List (BitVec 64 × BitVec 64) :=
  let table := BitVec.ofNat 64 start
  [(table + 48#64, usedAddress kind start capacity),
   (table + 56#64, BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)),
   (table + 64#64, BitVec.ofNat 64 (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity))]
def resultMemory (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (start capacity : Nat) : WordWrites.Memory :=
  WordWrites.write (clearMemory (WordWrites.write memory (beforeWrites kind start capacity)) be kind start capacity) (afterWrites kind start capacity)

theorem entered_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :
    (enteredState source kind start capacity).memory = resultMemory source.memory source.be kind start capacity := rfl

theorem entered_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :
    (enteredState source kind start capacity).clock = source.clock - price capacity := by
  change source.clock - 1 - 1 - 1 - 1 - TableNew.clearCost capacity - 1 - 1 = source.clock - (TableNew.clearCost capacity + 6)
  omega

/-- Full nonlocal state of the original generic constructor, including exact
heap reservation, header/clear memory and source-clock price. -/
theorem entered_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat) :
    emptyLocalsHOLFinite (enteredState source kind start capacity) = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (freshEnd kind start capacity))))
      memory := (resultMemory source.memory source.be kind start capacity)
      clock := source.clock - price capacity} := by
  have memory := entered_memory source kind start capacity
  have clock := entered_clock source kind start capacity
  rw [show emptyLocalsHOLFinite (enteredState source kind start capacity) = emptyLocalsHOLFinite
    {enteredState source kind start capacity with memory := (resultMemory source.memory source.be kind start capacity), clock := source.clock - price capacity}
    by rw [← memory, ← clock]]
  simp only [enteredState, finishState, backupState, orderStored, orderState, usedStored, clearState,
    usedState, valsStored, valsState, keysStored, keysState, initialState, headerState,
    PersistentAlloc.nextState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite, TableNew.update_twice]

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.entered_memory
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.entered_clock
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.entered_frame
