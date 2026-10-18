import InitECandidate.Solver.GasBudget.RecipientProgram
import InitECandidate.Solver.GasBudget.TxMessageRecord
import InitECandidate.Solver.PanFieldStoresFrame

namespace InitECandidate.Solver.GasBudget.Recipient
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable

def resultMemory (memory : WordWrites.Memory) (message recipient data length empty : BitVec 64) : WordWrites.Memory :=
  StoreWord.put (WordWrites.write memory (FieldStores.writes message (fields recipient data length empty))) (message + 104#64) recipient
def resultState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (message recipient data length empty : BitVec 64) :=
  {source with memory := resultMemory source.memory message recipient data length empty}

theorem field_bounds (recipient data length empty : BitVec 64) (field : FieldStores.Field) (member : field ∈ fields recipient data length empty) :
    field.offset + 8 ≤ 176 ∧ field.offset % 8 = 0 := by
  simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- The actual six non-creation message stores execute from the current
owned transaction record. Every copied read is protected from every write. -/
theorem fields_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (messageStart txStart : Nat) (recipient data length empty : BitVec 64)
    (region : MemoryRegion.Valid ⟨messageStart, 176⟩) (record : TxData source.memory txStart messageStart recipient data length)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 messageStart))))
    (txLocal : source.locals.lookup (ofString "tx") = some (.val (.word (BitVec.ofNat 64 txStart))))
    (emptyLocal : source.locals.lookup (ofString "empty") = some (.val (.word empty))) :
    evaluateHOLFiniteState source noncreateSetup = (none, resultState source (BitVec.ofNat 64 messageStart) recipient data length empty) := by
  let codeFields := fields recipient data length empty
  let message := BitVec.ofNat 64 messageStart
  let tx := BitVec.ofNat 64 txStart
  have copied := record.ready source txStart messageStart recipient data length domain txLocal
  have reads : ∀ field ∈ codeFields, field.value.Ready source "tx" tx := by
    intro field member
    simp only [codeFields, fields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact copied 152 recipient (by simp [txEntries])
    · exact copied 192 data (by simp [txEntries])
    · exact copied 200 length (by simp [txEntries])
    · exact emptyLocal
    · trivial
  have mapped : ∀ field ∈ codeFields, source.memaddrs (message + BitVec.ofNat 64 field.offset) := by
    intro field member
    rw [domain]
    have bounds := field_bounds recipient data length empty field member
    exact MemoryRegion.word_mapped ⟨messageStart, 176⟩ region field.offset bounds.1 bounds.2
  have separate : ∀ reader ∈ codeFields, ∀ writer ∈ codeFields, reader.value.Avoid tx (message + BitVec.ofNat 64 writer.offset) := by
    intro reader member writer inWriter
    have bounds := field_bounds recipient data length empty writer inWriter
    simp only [codeFields, fields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact record.message_away region 152 writer.offset (by decide) (by omega)
    · exact record.message_away region 192 writer.offset (by decide) (by omega)
    · exact record.message_away region 200 writer.offset (by decide) (by omega)
    · trivial
    · trivial
  let middle := {source with memory := WordWrites.write source.memory (FieldStores.writes message codeFields)}
  have first := FieldStores.execute source "m" "tx" message tx codeFields messageLocal reads mapped separate lastStore
  change evaluateHOLFiniteState source noncreateSetup = evaluateHOLFiniteState middle lastStore at first
  have readyLast : (FieldStores.Value.copied 152 recipient).Ready middle "tx" tx :=
    FieldStores.Value.ready_writes source message codeFields "tx" tx (.copied 152 recipient) (copied 152 recipient (by simp [txEntries]))
      (by intro writer member; have bounds := field_bounds recipient data length empty writer member; exact record.message_away region 152 writer.offset (by decide) (by omega))
  have valueRead := FieldStores.Value.read middle "tx" tx (.copied 152 recipient) readyLast
  have addressRead : eval middle (addConst (localVar "m") 104#64) = some (.val (.word (message + 104#64))) := by
    simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, messageLocal, valueIsWord, valueWord, wordOpHOL, wordOp, middle, message]
  have lastMapped : middle.memaddrs (message + 104#64) := by
    change source.memaddrs _
    rw [domain]
    exact MemoryRegion.word_mapped ⟨messageStart, 176⟩ region 104 (by change 104 + 8 ≤ 176; decide) (by decide)
  have last := StoreWord.execute middle _ RootMessage.recipientExpression _ recipient addressRead valueRead lastMapped
  change evaluateHOLFiniteState middle lastStore = (none, resultState source message recipient data length empty) at last
  rw [last] at first
  exact first

theorem result_outside (memory : WordWrites.Memory) (messageStart : Nat) (recipient data length empty query : BitVec 64)
    (region : MemoryRegion.Valid ⟨messageStart, 176⟩) (outside : query.toNat < messageStart ∨ messageStart + 176 ≤ query.toNat) :
    resultMemory memory (BitVec.ofNat 64 messageStart) recipient data length empty query = memory query := by
  have different : query ≠ BitVec.ofNat 64 messageStart + 104#64 := by
    intro same
    have numeric := congrArg BitVec.toNat same
    rw [MessageField.field_number messageStart 104 region (by decide)] at numeric
    omega
  rw [resultMemory, StoreWord.put, if_neg different]
  exact FieldStores.writes_outside memory ⟨messageStart, 176⟩ region (fields recipient data length empty)
    (by intro field member; have bounds := field_bounds recipient data length empty field member; change field.offset < 176; omega) query outside

theorem result_gas (memory : WordWrites.Memory) (message recipient data length empty : BitVec 64) :
    resultMemory memory message recipient data length empty (message + 40#64) = memory (message + 40#64) := by
  have away : message + 40#64 ∉ (FieldStores.writes message (fields recipient data length empty)).map Prod.fst := by
    simp [FieldStores.writes, fields, BitVec.add_right_inj]
  rw [resultMemory, StoreWord.put]
  simp only [BitVec.add_right_inj, show (40#64 : BitVec 64) ≠ 104#64 from by decide, ↓reduceIte]
  exact WordWrites.write_away memory _ _ away

end InitECandidate.Solver.GasBudget.Recipient

#print axioms InitECandidate.Solver.GasBudget.Recipient.field_bounds
#print axioms InitECandidate.Solver.GasBudget.Recipient.fields_execute
#print axioms InitECandidate.Solver.GasBudget.Recipient.result_outside
#print axioms InitECandidate.Solver.GasBudget.Recipient.result_gas
