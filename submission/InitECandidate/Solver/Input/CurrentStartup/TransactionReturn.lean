import InitECandidate.Solver.Input.CurrentStartup.VarListData
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CurrentStartup.TransactionReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record array : BitVec 64) (length start size : Nat) (value : ValueHOL 64) : Prop where
  context : PayloadWorkspace.Context input current pointer record length
  valid : ∀ position < 4, Offsets.ValidAt 540#64 (BitVec.ofNat 64 length) (Payload.offsetWords input) position
  txs : current.locals.lookup (ofString "txs") = some
    (VarList.pairValue (VarList.decodedArray array size) (VarList.decodedCount input start size))
  arrayAfter : record.toNat + 136 ≤ array.toNat
  records : VarList.Records current input pointer array start size
  startEq : start = 62 + Guest.GasLimit.le32 input 566
  sizeEq : size = Guest.GasLimit.le32 input 570 - Guest.GasLimit.le32 input 566
  inside : start + size ≤ input.length % 2^64
  memory : ∀ query : BitVec 64, query.toNat < record.toNat + 136 → current.memory query = caller.memory query
  price : caller.clock - current.clock ≤ size / 4 + 2
  clock : current.clock ≤ caller.clock
  returned : evaluateHOLFiniteState current Payload.afterTransactions = (some (.returned value), post)

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller current post, ∃ pointer record array : BitVec 64, ∃ length start size : Nat, ∃ value : ValueHOL 64,
    Result input caller current post pointer record array length start size value

/-- Resume the actual payload continuation after the real returned list. No
minimum caller clock or successful future store is assumed. -/
theorem returned (input : Guest.InputBlob) (actual : VarListData.Reached input) : Reached input := by
  classical
  obtain ⟨caller, entry, bodyPost, pointer, record, array, length, start, size, tuple, data⟩ := actual
  obtain ⟨callee, parentPost, value, entryEq, args, called, callerRun⟩ := data.invocation
  have scopedRun := callerRun
  rw [Payload.transactions_shape.2.1] at scopedRun
  have positive := CallNormal.normal_clock caller parentPost (ofString "txs") VarList.returnShape (ofString "ssz_split_var_list")
    Payload.transactionArguments Payload.afterTransactions value scopedRun
  have bodyRun := data.returned
  rw [entryEq] at bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact tuple) VarList.returnShape &&
      shapeEqHOL (shapeOfHOLExact tuple) VarList.returnShape) = true := by
    rw [data.tuple]
    simp [VarList.pairValue, VarList.returnShape, shapeOfHOLExact, shapeEqHOL_eq_true]
  have invoked := CallNormal.return_execute caller bodyPost "txs" VarList.returnShape (ofString "ssz_split_var_list")
    Payload.transactionArguments _ VarList.body Payload.afterTransactions callee VarList.returnShape tuple args called positive bodyRun shapePass
  have normal := invoked.symm.trans scopedRun
  let current := CallNormal.continuationEntry caller bodyPost "txs" tuple
  have resumed : (evaluateHOLFiniteState current Payload.afterTransactions).1 = some (.returned value) := congrArg Prod.fst normal
  let allocation := if size = 0 then caller else WitnessRadix.PersistentAlloc.post caller array
    (BitVec.ofNat 64 (16 * (Guest.GasLimit.le32 input start / 4)))
  have currentEq : current = setVarHOLFinite (ofString "txs") tuple
      {allocation with locals := caller.locals, memory := bodyPost.memory, clock := bodyPost.clock} := by
    have frame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
      setVarHOLFinite (ofString "txs") tuple {state with locals := caller.locals, memory := bodyPost.memory, clock := bodyPost.clock}) data.control
    rw [entryEq] at frame
    by_cases empty : size = 0
    · simp only [if_pos empty] at frame
      simpa only [allocation, if_pos empty, WitnessRadix.BackingLayout.control, emptyLocalsHOLFinite,
        callEntryStateHOLFinite, current, CallNormal.continuationEntry] using frame
    · simp only [if_neg empty] at frame
      simpa only [allocation, if_neg empty, WitnessRadix.BackingLayout.control, emptyLocalsHOLFinite,
        callEntryStateHOLFinite, current, CallNormal.continuationEntry, WitnessRadix.PersistentAlloc.post] using frame
  have bytes : Blob.HeapInput current input pointer := Blob.HeapInput.of_fields bodyPost current input pointer rfl rfl rfl data.bytes
  have heap : NormalHeapEffects.AtLeast (record.toNat + 136) current := data.heap
  have copyHeap : NormalHeapEffects.AtLeast (pointer.toNat + input.length % 2^64 + 8) current := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := heap
    exact ⟨cursor, cell, by have := data.context.recordLower; omega, high, aligned⟩
  have context : PayloadWorkspace.Context input current pointer record length := by
    have old := data.context
    have metadata : current.code = caller.code ∧ current.eshapes = caller.eshapes ∧ current.memaddrs = caller.memaddrs ∧
        current.be = caller.be ∧ current.globals.lookup (ofString "ssz_offs") = caller.globals.lookup (ofString "ssz_offs") ∧
        (∀ name : MlS, name ≠ ofString "txs" → current.locals.lookup name = caller.locals.lookup name) := by
      rw [currentEq]
      dsimp only [allocation]
      split <;> refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
      · rfl
      · intro name other
        simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm other]
      · simp [setVarHOLFinite, WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE,
          show ofString "heap_ptr" ≠ ofString "ssz_offs" from by decide]
      · intro name other
        simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm other]
    obtain ⟨code, shapes, domain, endian, workspace, locals⟩ := metadata
    exact ⟨code ▸ old.code, shapes ▸ old.shapes, domain.trans old.domain, endian.trans old.endian, bytes, copyHeap,
      workspace.trans old.workspace, (locals (ofString "p") (by decide)).trans old.p, (locals (ofString "len") (by decide)).trans old.len,
      (locals (ofString "pl") (by decide)).trans old.pl, (locals (ofString "o_extra") (by decide)).trans old.extra,
      (locals (ofString "o_txs") (by decide)).trans old.txs, (locals (ofString "o_wd") (by decide)).trans old.wd,
      (locals (ofString "o_bal") (by decide)).trans old.bal, old.lengthBound, old.extent, old.lower, old.aligned, old.room,
      old.minimum, old.sliceUpper, old.sliceEq, old.recordLower, old.recordAligned, old.recordRoom, heap⟩
  have entryClock : entry.clock = caller.clock - 1 := by rw [entryEq]; rfl
  refine ⟨caller, current, (evaluateHOLFiniteState current Payload.afterTransactions).2, pointer, record, array,
    length, start, size, value, ⟨context, data.valid, ?_, data.recordBefore, VarList.Records.of_memory bodyPost current input pointer array start size rfl data.records,
    data.startEq, data.sizeEq, data.inside, ?_, ?_, ?_, Prod.ext resumed rfl⟩⟩
  · change (caller.locals.update (ofString "txs", tuple)).lookup (ofString "txs") = _
    simp [HolFiniteMapExact.update, FUPDATE, data.tuple]
  · intro query before
    have saved := data.memory query (by have := data.recordBefore; omega)
    change bodyPost.memory query = caller.memory query
    rw [entryEq] at saved
    exact saved
  · change caller.clock - bodyPost.clock ≤ size / 4 + 2
    have price := data.price
    rw [entryClock] at price
    omega
  · change bodyPost.clock ≤ caller.clock
    have clock := data.clock
    rw [entryClock] at clock
    omega

theorem separated (input : Guest.InputBlob) (word : BitVec 64) (actual : MainSeparatedInput.StatelessRun input word) : Reached input :=
  returned input (VarListData.separated input word actual)

end InitECandidate.Solver.Input.CurrentStartup.TransactionReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.TransactionReturn.returned
#print axioms InitECandidate.Solver.Input.CurrentStartup.TransactionReturn.separated
