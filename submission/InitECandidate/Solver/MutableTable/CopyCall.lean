import InitECandidate.Solver.MutableTable.CopyPost
import InitECandidate.Solver.MutableTable.SingleCallEnvironment

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def formals : List (MlS × ShapeHOL) := [(ofString "t", .one)]

/-- Actual scalar htab_copy caller, including its allocation/copy cost,
returned new pointer, exact heap update and both physical table models. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (nextValid : Valid kind (fresh kind start old.capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (shape : old.capacity = 4 ∨ old.capacity % 8 = 0) (slots : List Nat) (occupied : MemoryModel.Occupied source kind old slots)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (tableCode : source.code.lookup (ofString "htab_copy") = some (formals, body, .one))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (ReadCall.singleValues (cell old .header 0)))
    (enough : price kind old.capacity + 1 ≤ source.clock) :
    ∃ memory,
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_copy") arguments continuation) =
        (let output := evaluateHOLFiniteState (bind (changed source kind old start (price kind old.capacity + 1) memory) name (BitVec.ofNat 64 start)) continuation
         (output.1, restore source name output.2)) ∧
      MemoryModel.Header memory kind (fresh kind start old.capacity) (BitVec.ofNat 64 slots.length) ∧
      MemoryModel.Occupied (changed source kind old start (price kind old.capacity + 1) memory) kind (fresh kind start old.capacity) slots ∧
      MemoryModel.PoolFrame source.memory memory kind old ∧
      MemoryModel.Occupied (changed source kind old start (price kind old.capacity + 1) memory) kind old slots ∧
      (∀ query : BitVec 64, query.toNat < start ∨ freshEnd kind start old.capacity ≤ query.toNat → memory query = source.memory query) := by
  obtain ⟨callee, called, tableLocal⟩ := ReadCall.single_environment source.code.lookup (ofString "htab_copy") body .one (cell old .header 0) tableCode
  let entry := callEntryStateHOLFinite source callee
  have entryModel := MemoryModel.Occupied.of_fields source entry kind old slots occupied rfl rfl rfl
  obtain ⟨memory, target, actual, frame, nextHeader, newModel, poolFrame, oldModel, outsideFrame⟩ := execute_model entry kind old oldValid start nextValid earlier domain little shape slots entryModel header tableLocal heap allocCode copyCode
    (by change price kind old.capacity ≤ source.clock - 1; omega)
  have updated := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have subtract : source.clock - 1 - price kind old.capacity = source.clock - (price kind old.capacity + 1) := by omega
  have replaced : {target with locals := source.locals} = changed source kind old start (price kind old.capacity + 1) memory := by
    simpa only [emptyLocalsHOLFinite, changed, entry, callEntryStateHOLFinite, subtract] using updated
  have resumed : Input.CallNormal.continuationEntry source target name (.val (.word (BitVec.ofNat 64 start))) =
      bind (changed source kind old start (price kind old.capacity + 1) memory) name (BitVec.ofNat 64 start) := by
    rw [Input.CallNormal.continuationEntry, replaced]
    rfl
  have callRun := Input.CallNormal.return_execute source target name .one (ofString "htab_copy") arguments _ body continuation callee .one
    (.val (.word (BitVec.ofNat 64 start))) args called (by omega) actual (by simp [shapeOfHOLExact, shapeEqHOL_eq_true])
  rw [resumed] at callRun
  refine ⟨memory, callRun, nextHeader, ?_, poolFrame, ?_, outsideFrame⟩
  · exact MemoryModel.Occupied.of_fields (changed entry kind old start (price kind old.capacity) memory)
      (changed source kind old start (price kind old.capacity + 1) memory) kind _ slots newModel rfl rfl rfl
  · exact MemoryModel.Occupied.of_fields (changed entry kind old start (price kind old.capacity) memory)
      (changed source kind old start (price kind old.capacity + 1) memory) kind old slots oldModel rfl rfl rfl

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.call_execute
