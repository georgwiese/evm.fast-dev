import InitECandidate.Solver.MutableTable.KeysExecution
import InitECandidate.Solver.MutableTable.SingleCallEnvironment

namespace InitECandidate.Solver.MutableTable.Keys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete original key-enumeration caller, heap reservation, real tuple
ABI, source-table model and full outside-output memory frame. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (start : Nat) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (outValid : MemoryRegion.Valid (outputRegion kind start slots.length)) (earlier : ∀ pool, plan.base pool + size kind plan pool ≤ start)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (keysCode : source.code.lookup (ofString "htab_keys") = some (formals, body, pairShape))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (ReadCall.singleValues (cell plan .header 0)))
    (enough : price kind slots.length + 1 ≤ source.clock) :
    ∃ paid memory, paid ≤ price kind slots.length + 1 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "htab_keys") arguments continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString name) (pair (BitVec.ofNat 64 start) (BitVec.ofNat 64 slots.length))
          (changed source kind start slots.length paid memory)) continuation
         (output.1, restore source name output.2)) ∧
      MemoryModel.PoolFrame source.memory memory kind plan ∧
      MemoryModel.Occupied (changed source kind start slots.length paid memory) kind plan slots ∧
      (∀ query : BitVec 64, query.toNat < start ∨ start + allocationSize kind slots.length ≤ query.toNat → memory query = source.memory query) := by
  obtain ⟨callee, called, tableLocal⟩ := ReadCall.single_environment source.code.lookup (ofString "htab_keys") body pairShape (cell plan .header 0) keysCode
  let entry := callEntryStateHOLFinite source callee
  have entryModel := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
  obtain ⟨paid, memory, target, bounded, actual, frame, poolFrame, finalModel, outsideFrame⟩ := execute entry kind plan valid domain start slots entryModel header outValid earlier tableLocal heap allocCode copyCode
    (by change price kind slots.length ≤ source.clock - 1; omega)
  have updated := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  have replaced : {target with locals := source.locals} = changed source kind start slots.length (paid + 1) memory := by
    simpa only [emptyLocalsHOLFinite, changed, entry, callEntryStateHOLFinite, subtract] using updated
  have resumed : Input.CallNormal.continuationEntry source target name (pair (BitVec.ofNat 64 start) (BitVec.ofNat 64 slots.length)) =
      setVarHOLFinite (ofString name) (pair (BitVec.ofNat 64 start) (BitVec.ofNat 64 slots.length)) (changed source kind start slots.length (paid + 1) memory) := by
    rw [Input.CallNormal.continuationEntry, replaced]
  have callRun := Input.CallNormal.return_execute source target name pairShape (ofString "htab_keys") arguments _ body continuation callee pairShape
    (pair (BitVec.ofNat 64 start) (BitVec.ofNat 64 slots.length)) args called (by omega) actual (by simp [pair, pairShape, shapeOfHOLExact, shapeEqHOL_eq_true])
  rw [resumed] at callRun
  refine ⟨paid + 1, memory, by omega, callRun, poolFrame, ?_, outsideFrame⟩
  exact MemoryModel.Occupied.of_pool_frame source _ kind plan valid slots occupied rfl rfl poolFrame

theorem caller_price (kind : KeyHash.Kind) (count : Nat) : price kind count + 1 =
    (match kind with | .account => 5 | .indexedAccount => 6 | .word => 6 | .storage => 9 | .indexedStorage => 10) * count + 2 := by
  cases kind <;> dsimp only [price, rowPrice, stride, KeyHash.keySize] <;> omega

end InitECandidate.Solver.MutableTable.Keys

#print axioms InitECandidate.Solver.MutableTable.Keys.call_execute
#print axioms InitECandidate.Solver.MutableTable.Keys.caller_price
