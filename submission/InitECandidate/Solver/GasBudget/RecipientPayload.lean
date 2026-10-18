import InitECandidate.Solver.GasBudget.RecipientFields
import InitECandidate.Solver.GasBudget.RecipientLinks

namespace InitECandidate.Solver.GasBudget.Recipient
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable

theorem result_code (memory : WordWrites.Memory) (message recipient data length empty : BitVec 64) :
    resultMemory memory message recipient data length empty (message + 112#64) = .word empty := by
  simp [resultMemory, FieldStores.writes, fields, FieldStores.Value.word, WordWrites.write, StoreWord.put, BitVec.add_right_inj]

theorem result_length (memory : WordWrites.Memory) (message recipient data length empty : BitVec 64) :
    resultMemory memory message recipient data length empty (message + 120#64) = .word 0#64 := by
  simp [resultMemory, FieldStores.writes, fields, FieldStores.Value.word, WordWrites.write, StoreWord.put, BitVec.add_right_inj]

theorem result_reservoir (memory : WordWrites.Memory) (message recipient data length empty : BitVec 64) :
    resultMemory memory message recipient data length empty (message + 48#64) = memory (message + 48#64) := by
  simp [resultMemory, FieldStores.writes, fields, FieldStores.Value.word, WordWrites.write, StoreWord.put, BitVec.add_right_inj]

theorem linked_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start field : Nat) (aa ak : BitVec 64)
    (inside : field < 176) (notAA : field ≠ 152) (notAK : field ≠ 160) :
    (linkedState source start aa ak).memory (BitVec.ofNat 64 start + BitVec.ofNat 64 field) = source.memory (BitVec.ofNat 64 start + BitVec.ofNat 64 field) := by
  exact (MessageField.scalar_other _ start 160 field ak notAK (by omega) (by decide)).trans
    (MessageField.scalar_other source start 152 field aa notAA (by omega) (by decide))

end InitECandidate.Solver.GasBudget.Recipient

#print axioms InitECandidate.Solver.GasBudget.Recipient.result_code
#print axioms InitECandidate.Solver.GasBudget.Recipient.result_length
#print axioms InitECandidate.Solver.GasBudget.Recipient.result_reservoir
#print axioms InitECandidate.Solver.GasBudget.Recipient.linked_other
