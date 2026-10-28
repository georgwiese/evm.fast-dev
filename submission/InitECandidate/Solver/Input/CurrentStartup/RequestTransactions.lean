import InitECandidate.Solver.Input.CurrentStartup.RequestMetadataCells
import InitECandidate.Solver.Input.PayloadTransactionFrame

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch
variable {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
variable {source current post caller entry : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {pointer statelessRecord record gasWord count : BitVec 64}
variable {length payloadLength start size : Nat} {value : ValueHOL 64}

/-- The actual SI0 store and fixed-list count call preserve the complete
transaction image returned by the same payload invocation. -/
theorem HashCountReturn.Result.transactions
    (data : HashCountReturn.Result (decoderOrigin := decoderOrigin) input source current post
      pointer statelessRecord record gasWord count length value) :
    ∃ array start size, Payload.TransactionImage input current pointer record array start size := by
  obtain ⟨origin, originalPost, stored, previous, storedRun, frame, endpoint⟩ := data.origin
  obtain ⟨array, start, size, transactions⟩ := previous.transactions
  have context := previous.context
  obtain ⟨run, storedContext⟩ := context.stateless_store input source pointer statelessRecord record gasWord length 0
    (localVar "pl") record (by decide) (by decide) (Request.local_word source "pl" record context.pl)
  change evaluateHOLFiniteState source Request.payloadPointerStore = _ at run
  have same := congrArg Prod.snd (storedRun.symm.trans run)
  dsimp only at same
  have storedImage : Payload.TransactionImage input stored pointer record array start size := by
    rw [same]
    simpa using transactions.store_before statelessRecord record (by have := context.recordAfter; omega)
  exact ⟨array, start, size, storedImage.of_frame frame⟩

/-- The same three real SI metadata stores precede the request call and
leave its complete payload transaction image and allocator extent intact. -/
theorem RequestsEntry.Result.transactions
    (data : RequestsEntry.Result (decoderOrigin := decoderOrigin) input caller entry post
      pointer statelessRecord record gasWord payloadLength start size value) :
    ∃ array start size, Payload.TransactionImage input caller pointer record array start size := by
  obtain ⟨origin, hashSource, hashPost, count, parentValue, hashes, callerEq⟩ := data.stores
  obtain ⟨array, txStart, txSize, transactions⟩ := hashes.transactions
  have context := hashes.context
  have before (offset : Nat) (small : offset ≤ 24) :
      (statelessRecord + BitVec.ofNat 64 offset).toNat < record.toNat := by
    rw [context.si_field_number input hashSource pointer statelessRecord record gasWord payloadLength offset (by omega)]
    have := context.recordAfter
    omega
  have first := transactions.store_before (statelessRecord + 8#64) (pointer + 18#64 + Request.requestWords input 1) (before 8 (by decide))
  have second := first.store_before (statelessRecord + 16#64) count (before 16 (by decide))
  have third := second.store_before (statelessRecord + 24#64) (pointer + 18#64 + 8#64) (before 24 (by decide))
  refine ⟨array, txStart, txSize, ?_⟩
  rw [callerEq]
  exact third

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.HashCountReturn.Result.transactions

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsEntry.Result.transactions
