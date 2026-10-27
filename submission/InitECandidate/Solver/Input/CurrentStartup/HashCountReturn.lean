import InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
import InitECandidate.Solver.Input.RequestHashesProgram

namespace InitECandidate.Solver.Input.CurrentStartup.HashCountReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord count : BitVec 64) (length : Nat) (value : ValueHOL 64) : Prop where
  context : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord length
  nvh : current.locals.lookup (ofString "nvh") = some (.val (.word count))
  countEq : count.toNat = (Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) / 32
  countFits : (Guest.GasLimit.le32 input 58 - Guest.GasLimit.le32 input 22) % 32 = 0
  price : source.clock - current.clock ≤ 66
  clock : current.clock ≤ source.clock
  returned : evaluateHOLFiniteState current Request.afterHashCount = (some (.returned value), post)

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ source current post, ∃ pointer statelessRecord record gasWord count : BitVec 64, ∃ length : Nat, ∃ value : ValueHOL 64,
    Result input source current post pointer statelessRecord record gasWord count length value

/-- The real versioned-hash count call preserves the allocated payload and
its bounded gas word. Arithmetic follows from actual validated request offsets. -/
theorem payload (input : Guest.InputBlob) (actual : PayloadCallerReturn.Reached input) : Reached input := by
  classical
  obtain ⟨caller, source, post, pointer, statelessRecord, record, gasWord, length, value, data⟩ := actual
  have context := data.context
  have read : eval source (localVar "pl") = some (.val (.word record)) := Request.local_word source "pl" record context.pl
  obtain ⟨storedRun, storedContext⟩ := context.stateless_store input source pointer statelessRecord record gasWord length 0
    (localVar "pl") record (by decide) (by decide) read
  let stored := {source with memory := WitnessRadix.StoreWord.put source.memory (statelessRecord + BitVec.ofNat 64 0) record}
  have args := Request.hash_count_arguments stored input storedContext.request.vh storedContext.request.rq
  have actual := data.returned
  change evaluateHOLFiniteState source Request.payloadPointerStore = (none, stored) at storedRun
  rw [Request.hash_count_shape.1, WitnessRadix.StateSteps.next_sequence source stored _ _ storedRun (Nat.le_refl _), Request.hash_count_shape.2] at actual
  obtain ⟨current, innerPost, count, locals, countBound, frame, price, clock, remaining, postEq, arithmetic⟩ :=
    FixedList.caller_any_clock stored post (Request.requestWords input 2 - Request.requestWords input 1) 32#64 9223372036854775807#64
      (by decide) (WithdrawalReturn.division_code stored.code storedContext.code) (CanonicalHeader.fail_code stored.code storedContext.code)
      (storedContext.shapes .SszErr) (WithdrawalReturn.fixed_code stored.code storedContext.code) "nvh" Request.hashCountArguments Request.afterHashCount args value actual
  have valid := context.request.valid 2 (by decide)
  have ordered := valid.2.2 (by decide)
  change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22)).toNat ≤ (BitVec.ofNat 64 (Guest.GasLimit.le32 input 58)).toNat at ordered
  rw [Request.le32_number input 22 (by decide), Request.le32_number input 58 (by decide)] at ordered
  have difference := BitVec.toNat_sub_of_le
    (show Request.requestWords input 1 ≤ Request.requestWords input 2 from by
      change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22)).toNat ≤ (BitVec.ofNat 64 (Guest.GasLimit.le32 input 58)).toNat
      rw [Request.le32_number input 22 (by decide), Request.le32_number input 58 (by decide)]; exact ordered)
  change (Request.requestWords input 2 - Request.requestWords input 1).toNat =
    (BitVec.ofNat 64 (Guest.GasLimit.le32 input 58)).toNat - (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22)).toNat at difference
  rw [Request.le32_number input 58 (by decide), Request.le32_number input 22 (by decide)] at difference
  obtain ⟨countEq, countFits⟩ := arithmetic (by decide)
  rw [difference] at countEq countFits
  refine ⟨source, current, innerPost, pointer, statelessRecord, record, gasWord, count, length, value,
    ⟨storedContext.bind_frame input stored current pointer statelessRecord record gasWord length (ofString "nvh") (.val (.word count))
      frame locals (by decide), ?_, countEq, countFits, price, clock, remaining⟩⟩
  rw [locals]
  simp [HolFiniteMapExact.update, FUPDATE]

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  payload input (PayloadCallerReturn.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.HashCountReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.HashCountReturn.payload
#print axioms InitECandidate.Solver.Input.CurrentStartup.HashCountReturn.separated
