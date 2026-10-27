import InitECandidate.Solver.Input.CurrentStartup.PayloadStoreFrame
import InitECandidate.Solver.Input.PayloadTransactionsProgram

namespace InitECandidate.Solver.Input.CurrentStartup.TransactionEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller entry post, ∃ pointer record : BitVec 64, ∃ length start size : Nat, ∃ returned : ValueHOL 64,
    PayloadWorkspace.Context input caller pointer record length ∧
    (∀ position < 4, Offsets.ValidAt 540#64 (BitVec.ofNat 64 length) (Payload.offsetWords input) position) ∧
    OriginalCode.Installed entry.code ∧ OriginalExceptions.Installed entry.eshapes ∧
    entry.memaddrs = InitE.ordinaryDomain ∧ entry.be = false ∧ entry.globals = caller.globals ∧
    Blob.HeapInput entry input pointer ∧ NormalHeapEffects.AtLeast (record.toNat + 136) entry ∧
    entry.locals.lookup (ofString "p") = some (.val (.word (pointer + BitVec.ofNat 64 start))) ∧
    entry.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 size))) ∧
    entry.locals.lookup (ofString "lim") = some (.val (.word 9223372036854775807#64)) ∧
    start = 62 + Guest.GasLimit.le32 input 566 ∧ size = Guest.GasLimit.le32 input 570 - Guest.GasLimit.le32 input 566 ∧
    start + size ≤ input.length % 2^64 ∧ evaluateHOLFiniteState entry VarList.body = (some (.returned returned), post) ∧
    ∃ callee parentPost parentValue,
      entry = callEntryStateHOLFinite caller callee ∧
      evalListHOLFinite caller (h := fun address => Classical.propDecidable (caller.memaddrs address)) Payload.transactionArguments =
        some (VarList.values (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 size) 9223372036854775807#64) ∧
      lookupCodeHOLFinite caller.code.lookup (ofString "ssz_split_var_list")
        (VarList.values (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 size) 9223372036854775807#64) =
        some (VarList.body, callee, VarList.returnShape) ∧
      evaluateHOLFiniteState caller Payload.transactionCall = (some (.returned parentValue), parentPost)

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ssz_split_var_list") = some (VarList.formals, VarList.body, VarList.returnShape) := by
  simpa only [Code.name, Code.body, Code.formals, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_ssz_split_var_list, VarList.formals, VarList.body, VarList.returnShape,
    shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
    using Code.installed code installed .ssz_split_var_list

/-- The real extra-data stores retain input and the payload record. Actual
return then exposes the genuine transaction-list callee and a contained slice;
no whole-array allocation room or future list return is assumed. -/
theorem extra_reached (input : Guest.InputBlob) (actual : PayloadExtra.Reached input) : Reached input := by
  obtain ⟨source, post, pointer, record, length, value, context, first, valid, extraBound, actual⟩ := actual
  rw [Payload.transactions_shape.1] at actual
  have safePointer : LocalPrefix (ofString "pl") Payload.extraPointerStore := .store _ _
  obtain ⟨firstState, firstRun, remaining, pl⟩ := safePointer.normal_continue source post (.seq Payload.extraLengthStore Payload.transactionCall) value actual
  have readRecord : eval source (localVar "pl") = some (.val (.word record)) := by
    simpa [eval, localVar, evalHOLExact, toExact] using context.pl
  have firstAddress := Scalar.plus_read source (localVar "pl") record 16 readRecord
  have firstContext := PayloadWorkspace.Context.op_store input source firstState pointer record length 16 _ .add _ context (by decide) firstAddress firstRun
  have safeLength : LocalPrefix (ofString "pl") Payload.extraLengthStore := .store _ _
  obtain ⟨current, secondRun, remaining, pl⟩ := safeLength.normal_continue firstState post Payload.transactionCall value remaining
  have readNextRecord : eval firstState (localVar "pl") = some (.val (.word record)) := by
    simpa [eval, localVar, evalHOLExact, toExact] using firstContext.pl
  have secondAddress := Scalar.plus_read firstState (localVar "pl") record 24 readNextRecord
  have currentContext := PayloadWorkspace.Context.op_store input firstState current pointer record length 24 _ .sub _ firstContext (by decide) secondAddress secondRun
  have secondValid := valid 2 (by decide)
  have ordered := secondValid.2.2 (by decide)
  change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)).toNat ≤ (BitVec.ofNat 64 (Guest.GasLimit.le32 input 570)).toNat at ordered
  rw [Request.le32_number input 566 (by decide), Request.le32_number input 570 (by decide)] at ordered
  have contained := secondValid.2.1
  change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 570)).toNat ≤ (BitVec.ofNat 64 length).toNat at contained
  have lengthSmall : length < 2^64 := by have := context.sliceUpper; have := Nat.mod_lt input.length (show 0 < 2^64 by decide); omega
  rw [Request.le32_number input 570 (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthSmall] at contained
  have inside : 62 + Guest.GasLimit.le32 input 570 ≤ input.length % 2^64 := by have := context.sliceUpper; have := context.extent; omega
  obtain ⟨args, sliceUpper⟩ := Payload.transaction_arguments current input pointer currentContext.p currentContext.txs currentContext.wd ordered inside
  obtain ⟨callee, called, pCell, lenCell, limCell⟩ := VarList.environment current.code.lookup
    (pointer + BitVec.ofNat 64 (62 + Guest.GasLimit.le32 input 566))
    (BitVec.ofNat 64 (Guest.GasLimit.le32 input 570 - Guest.GasLimit.le32 input 566)) 9223372036854775807#64
    (original_code current.code currentContext.code)
  have callerRun := remaining
  rw [Payload.transactions_shape.2.1] at remaining
  have positive := CallNormal.normal_clock current post (ofString "txs") VarList.returnShape (ofString "ssz_split_var_list")
    Payload.transactionArguments Payload.afterTransactions value remaining
  obtain ⟨bodyPost, returned, bodyRun⟩ := CallNormal.callee_return current post (ofString "txs") VarList.returnShape (ofString "ssz_split_var_list")
    Payload.transactionArguments _ VarList.body Payload.afterTransactions callee VarList.returnShape args called positive value remaining
  let entry := callEntryStateHOLFinite current callee
  have entryCode : OriginalCode.Installed entry.code := currentContext.code
  have entryShapes : OriginalExceptions.Installed entry.eshapes := currentContext.shapes
  have image : Blob.HeapInput entry input pointer := Blob.HeapInput.of_fields current entry input pointer rfl rfl rfl currentContext.image
  exact ⟨current, entry, bodyPost, pointer, record, length, 62 + Guest.GasLimit.le32 input 566,
    Guest.GasLimit.le32 input 570 - Guest.GasLimit.le32 input 566, returned, currentContext, valid, entryCode, entryShapes,
    currentContext.domain, currentContext.endian, rfl, image, currentContext.recordHeap, pCell, lenCell, limCell, rfl, rfl, sliceUpper, bodyRun, callee, post, value, rfl, args, called, callerRun⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64) (actual : MainSeparatedInput.StatelessRun input word) : Reached input :=
  extra_reached input (PayloadExtra.separated input word actual)

end InitECandidate.Solver.Input.CurrentStartup.TransactionEntry

#print axioms InitECandidate.Solver.Input.CurrentStartup.TransactionEntry.original_code
#print axioms InitECandidate.Solver.Input.CurrentStartup.TransactionEntry.extra_reached
#print axioms InitECandidate.Solver.Input.CurrentStartup.TransactionEntry.separated
