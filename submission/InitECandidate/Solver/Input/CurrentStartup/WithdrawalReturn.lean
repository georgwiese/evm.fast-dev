import InitECandidate.Solver.Input.CurrentStartup.TransactionReturn
import InitECandidate.Solver.Input.FixedList.NormalAnyClock
import InitECandidate.Solver.Input.PayloadTransactionStores
import InitECandidate.Solver.Input.VarList.RecordsAfterFrame

namespace InitECandidate.Solver.Input.CurrentStartup.WithdrawalReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record array count : BitVec 64) (length start size : Nat) (value : ValueHOL 64) : Prop where
  context : PayloadWorkspace.Context input current pointer record length
  valid : ∀ position < 4, Offsets.ValidAt 540#64 (BitVec.ofNat 64 length) (Payload.offsetWords input) position
  nwd : current.locals.lookup (ofString "nwd") = some (.val (.word count))
  txs : current.memory (record + 32#64) = .word (VarList.decodedArray array size)
  txCount : current.memory (record + 40#64) = .word (BitVec.ofNat 64 (VarList.decodedCount input start size))
  arrayAfter : record.toNat + 136 ≤ array.toNat
  records : VarList.Records current input pointer array start size
  startEq : start = 62 + Guest.GasLimit.le32 input 566
  sizeEq : size = Guest.GasLimit.le32 input 570 - Guest.GasLimit.le32 input 566
  inside : start + size ≤ input.length % 2^64
  countEq : count.toNat = (Payload.offsetWords input 3 - Payload.offsetWords input 2).toNat / 44
  countFits : (Payload.offsetWords input 3 - Payload.offsetWords input 2).toNat % 44 = 0
  price : source.clock - current.clock ≤ 66
  clock : current.clock ≤ source.clock
  returned : evaluateHOLFiniteState current Payload.afterWithdrawals = (some (.returned value), post)

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ source current post, ∃ pointer record array count : BitVec 64, ∃ length start size : Nat, ∃ value : ValueHOL 64,
    Result input source current post pointer record array count length start size value

theorem fixed_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ssz_fixed_list_count") = some (FixedList.formals, FixedList.body, .one) := by
  simpa only [Code.name, Code.body, Code.formals, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_ssz_fixed_list_count, FixedList.formals, FixedList.body, shapeToHOL, paramToHOL,
    List.map_cons, List.map_nil] using Code.installed code installed .ssz_fixed_list_count

theorem division_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "udivmod") = some (UDivMod.formals, UDivMod.body, UDivMod.returnShape) := by
  simpa only [Code.name, Code.body, Code.formals, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_udivmod, UDivMod.formals, UDivMod.body, UDivMod.returnShape, shapeToHOL, paramToHOL,
    List.map_cons, List.map_nil] using Code.installed code installed .udivmod

/-- Store the actual transaction result and resume after the real withdrawal
count call. Copied input and initialized transaction records remain available. -/
theorem transaction (input : Guest.InputBlob) (actual : TransactionReturn.Reached input) : Reached input := by
  classical
  obtain ⟨caller, source, post, pointer, record, array, length, start, size, value, data⟩ := actual
  let records := VarList.decodedArray array size
  let transactionCount := BitVec.ofNat 64 (VarList.decodedCount input start size)
  have firstRead : eval source (.rfield 0 (localVar "txs")) = some (.val (.word records)) := by
    simp [eval, localVar, VarList.pairValue, evalHOLExact, toExact, data.txs, records]
  obtain ⟨firstRun, firstContext, firstCell, firstFrame⟩ := data.context.field_store input source pointer record length
    32 (.rfield 0 (localVar "txs")) records (by decide) (by decide) firstRead
  let first := Payload.fieldStored source record 32 records
  have secondRead : eval first (.rfield 1 (localVar "txs")) = some (.val (.word transactionCount)) := by
    have cell : first.locals.lookup (ofString "txs") = some
        (VarList.pairValue (VarList.decodedArray array size) (VarList.decodedCount input start size)) := data.txs
    simp [eval, localVar, VarList.pairValue, evalHOLExact, toExact, cell, transactionCount]
  obtain ⟨secondRun, storedContext, secondCell, secondFrame⟩ := firstContext.field_store input first pointer record length
    40 (.rfield 1 (localVar "txs")) transactionCount (by decide) (by decide) secondRead
  let stored := Payload.fieldStored first record 40 transactionCount
  change evaluateHOLFiniteState source Payload.transactionPointerStore = (none, first) at firstRun
  change evaluateHOLFiniteState first Payload.transactionCountStore = (none, stored) at secondRun
  have firstAddress : (record + 32#64).toNat = record.toNat + 32 := by
    apply BitVec.toNat_add_of_lt
    change record.toNat + _ < 2^64
    norm_num
    have := data.context.recordRoom
    omega
  have secondAddress : (record + 40#64).toNat = record.toNat + 40 := by
    apply BitVec.toNat_add_of_lt
    change record.toNat + _ < 2^64
    norm_num
    have := data.context.recordRoom
    omega
  have firstRecords : VarList.Records first input pointer array start size :=
    VarList.Records.store_before source input pointer array (record + 32#64) records start size data.records (by rw [firstAddress]; have := data.arrayAfter; omega)
  have storedRecords : VarList.Records stored input pointer array start size :=
    VarList.Records.store_before first input pointer array (record + 40#64) transactionCount start size firstRecords (by rw [secondAddress]; have := data.arrayAfter; omega)
  have storedRun : evaluateHOLFiniteState stored Payload.withdrawalCall = (some (.returned value), post) := by
    have actual := data.returned
    rw [Payload.transactions_shape.2.2.1,
      WitnessRadix.StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence first stored _ _ secondRun (Nat.le_refl _)] at actual
    exact actual
  have args := Payload.withdrawal_arguments stored (Payload.offsetWords input 2) (Payload.offsetWords input 3) storedContext.wd storedContext.bal
  rw [Payload.transactions_shape.2.2.2] at storedRun
  obtain ⟨current, innerPost, count, locals, limit, frozen, price, clock, remaining, postEq, arithmetic⟩ :=
    FixedList.caller_any_clock stored post (Payload.offsetWords input 3 - Payload.offsetWords input 2) 44#64 9223372036854775807#64
      (by decide) (division_code stored.code storedContext.code) (CanonicalHeader.fail_code stored.code storedContext.code)
      (storedContext.shapes .SszErr) (fixed_code stored.code storedContext.code) "nwd" Payload.withdrawalArguments Payload.afterWithdrawals args value storedRun
  have currentEq : current = {stored with locals := stored.locals.update (ofString "nwd", .val (.word count)), clock := current.clock} := by
    have frame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := current.locals, clock := current.clock}) frozen
    change current = {stored with locals := current.locals, clock := current.clock} at frame
    rw [locals] at frame
    exact frame
  have currentContext : PayloadWorkspace.Context input current pointer record length := by
    rw [currentEq]
    apply PayloadWorkspace.Context.locals_clock input stored pointer record length current.clock _ storedContext
    intro name kept
    simp only [List.mem_cons, List.not_mem_nil, or_false] at kept
    rcases kept with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [HolFiniteMapExact.update, FUPDATE, show ofString "nwd" ≠ ofString "p" from by decide,
        show ofString "nwd" ≠ ofString "len" from by decide, show ofString "nwd" ≠ ofString "pl" from by decide,
        show ofString "nwd" ≠ ofString "o_extra" from by decide, show ofString "nwd" ≠ ofString "o_txs" from by decide,
        show ofString "nwd" ≠ ofString "o_wd" from by decide, show ofString "nwd" ≠ ofString "o_bal" from by decide]
  have memory : current.memory = stored.memory := by rw [currentEq]
  refine ⟨source, current, innerPost, pointer, record, array, count, length, start, size, value,
    ⟨currentContext, data.valid, ?_, ?_, ?_, data.arrayAfter, VarList.Records.of_memory stored current input pointer array start size memory storedRecords,
    data.startEq, data.sizeEq, data.inside, (arithmetic (by decide)).1, (arithmetic (by decide)).2, price, clock, remaining⟩⟩
  · rw [locals]
    simp [HolFiniteMapExact.update, FUPDATE]
  · rw [memory]
    exact (secondFrame (record + 32#64) (by intro same; have := congrArg BitVec.toNat same; omega)).trans firstCell
  · rw [memory]
    exact secondCell

theorem separated (input : Guest.InputBlob) (word : BitVec 64) (actual : MainSeparatedInput.StatelessRun input word) : Reached input :=
  transaction input (TransactionReturn.separated input word actual)

end InitECandidate.Solver.Input.CurrentStartup.WithdrawalReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.WithdrawalReturn.fixed_code
#print axioms InitECandidate.Solver.Input.CurrentStartup.WithdrawalReturn.division_code
#print axioms InitECandidate.Solver.Input.CurrentStartup.WithdrawalReturn.transaction
#print axioms InitECandidate.Solver.Input.CurrentStartup.WithdrawalReturn.separated
