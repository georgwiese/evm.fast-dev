import InitECandidate.Solver.GasBudget.MessageFieldFrame
import InitECandidate.Solver.MutableTable.MemoryRegionWord
import InitECandidate.Solver.PanFieldStores

namespace InitECandidate.Solver.GasBudget.Recipient
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable

def txEntries (recipient data length : BitVec 64) : List (Nat × BitVec 64) := [(152, recipient), (192, data), (200, length)]
structure TxData (memory : WordWrites.Memory) (start message : Nat) (recipient data length : BitVec 64) : Prop where
  valid : MemoryRegion.Valid ⟨start, 400⟩
  earlier : start + 400 ≤ message
  words : ∀ offset value, (offset, value) ∈ txEntries recipient data length → memory (BitVec.ofNat 64 start + BitVec.ofNat 64 offset) = .word value

theorem tx_entry_bounds (recipient data length : BitVec 64) (offset : Nat) (value : BitVec 64) (member : (offset, value) ∈ txEntries recipient data length) :
    offset + 8 ≤ 400 ∧ offset % 8 = 0 := by
  simp only [txEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

theorem TxData.field_number {memory : WordWrites.Memory} {start message : Nat} {recipient data length : BitVec 64}
    (record : TxData memory start message recipient data length) (offset : Nat) (inside : offset ≤ 400) :
    (BitVec.ofNat 64 start + BitVec.ofNat 64 offset).toNat = start + offset := by
  rw [← BitVec.ofNat_add]
  exact MemoryRegion.address_number ⟨start, 400⟩ record.valid offset inside

theorem TxData.ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start message : Nat) (recipient data length : BitVec 64)
    (record : TxData source.memory start message recipient data length) (domain : source.memaddrs = InitE.ordinaryDomain)
    (txLocal : source.locals.lookup (ofString "tx") = some (.val (.word (BitVec.ofNat 64 start)))) :
    ∀ offset value, (offset, value) ∈ txEntries recipient data length → (FieldStores.Value.copied offset value).Ready source "tx" (BitVec.ofNat 64 start) := by
  intro offset value member
  have bounds := tx_entry_bounds recipient data length offset value member
  refine ⟨txLocal, ?_, record.words offset value member⟩
  rw [domain]
  exact MemoryRegion.word_mapped ⟨start, 400⟩ record.valid offset bounds.1 bounds.2

theorem TxData.of_protected {source target : WordWrites.Memory} {start message : Nat} {recipient data length : BitVec 64}
    (record : TxData source start message recipient data length)
    (frame : ∀ query : BitVec 64, query.toNat < message → target query = source query) : TxData target start message recipient data length := by
  refine ⟨record.valid, record.earlier, ?_⟩
  intro offset value member
  have bounds := tx_entry_bounds recipient data length offset value member
  rw [frame _ (by rw [record.field_number offset (by omega)]; have before := record.earlier; omega)]
  exact record.words offset value member

/-- Transaction field reads and fresh message destinations cannot alias. -/
theorem TxData.message_away {memory : WordWrites.Memory} {start message : Nat} {recipient data length : BitVec 64}
    (record : TxData memory start message recipient data length) (region : MemoryRegion.Valid ⟨message, 176⟩)
    (offset destination : Nat) (inside : offset + 8 ≤ 400) (destinationInside : destination < 176) :
    BitVec.ofNat 64 start + BitVec.ofNat 64 offset ≠ BitVec.ofNat 64 message + BitVec.ofNat 64 destination := by
  intro same
  have numeric := congrArg BitVec.toNat same
  rw [record.field_number offset (by omega), MessageField.field_number message destination region (by omega)] at numeric
  have before := record.earlier
  omega

end InitECandidate.Solver.GasBudget.Recipient

#print axioms InitECandidate.Solver.GasBudget.Recipient.tx_entry_bounds
#print axioms InitECandidate.Solver.GasBudget.Recipient.TxData.field_number
#print axioms InitECandidate.Solver.GasBudget.Recipient.TxData.ready
#print axioms InitECandidate.Solver.GasBudget.Recipient.TxData.of_protected
#print axioms InitECandidate.Solver.GasBudget.Recipient.TxData.message_away
