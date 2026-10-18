import InitECandidate.Solver.GasBudget.RecipientFields
import InitECandidate.Solver.MutableTable.TableStateFrame

namespace InitECandidate.Solver.GasBudget.Recipient
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

theorem condition_false (source : PanSemStateFiniteExact 64 Guest.HostMemory) (messageStart txStart : Nat)
    (recipient data length : BitVec 64) (record : TxData source.memory txStart messageStart recipient data length)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (txLocal : source.locals.lookup (ofString "tx") = some (.val (.word (BitVec.ofNat 64 txStart))))
    (nonzero : recipient ≠ 0#64) : eval source condition = some (.val (.word 0#64)) := by
  have ready := record.ready source txStart messageStart recipient data length domain txLocal 152 recipient (by simp [txEntries])
  have read := FieldStores.Value.read source "tx" (BitVec.ofNat 64 txStart) (.copied 152 recipient) ready
  change eval source RootMessage.recipientExpression = some (.val (.word recipient)) at read
  simp only [eval] at read ⊢
  rw [condition, evalHOLExact, read]
  simp [evalHOLExact, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero]

/-- The actual recipient test takes the non-creation branch and executes all
six stores; this part of the original source consumes no evaluator clock. -/
theorem noncreate_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (messageStart txStart : Nat)
    (recipient data length empty : BitVec 64) (region : MemoryRegion.Valid ⟨messageStart, 176⟩)
    (record : TxData source.memory txStart messageStart recipient data length) (domain : source.memaddrs = InitE.ordinaryDomain)
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 messageStart))))
    (txLocal : source.locals.lookup (ofString "tx") = some (.val (.word (BitVec.ofNat 64 txStart))))
    (emptyLocal : source.locals.lookup (ofString "empty") = some (.val (.word empty))) (nonzero : recipient ≠ 0#64) :
    evaluateHOLFiniteState source afterEmpty = evaluateHOLFiniteState
      (resultState source (BitVec.ofNat 64 messageStart) recipient data length empty) afterChoice := by
  have test := condition_false source messageStart txStart recipient data length record domain txLocal nonzero
  have choice : evaluateHOLFiniteState source (.ite condition creationSetup noncreateSetup) =
      (none, resultState source (BitVec.ofNat 64 messageStart) recipient data length empty) := by
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite, test]
    simpa using fields_execute source messageStart txStart recipient data length empty region record domain messageLocal txLocal emptyLocal
  rw [choice_shape, StateSteps.next_sequence source _ _ _ choice (Nat.le_refl _)]

theorem result_recipient (memory : WordWrites.Memory) (message recipient data length empty : BitVec 64) :
    resultMemory memory message recipient data length empty (message + 32#64) = .word recipient := by
  simp [resultMemory, FieldStores.writes, fields, FieldStores.Value.word, WordWrites.write, StoreWord.put, BitVec.add_right_inj]

/-- The initialized message lies before every live table pool, so its stores
retain both tables, including used-byte reads and inverse order positions. -/
theorem result_table (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor messageStart : Nat) (recipient data length empty : BitVec 64)
    (table : TableState source kind plan slots cursor floor) (region : MemoryRegion.Valid ⟨messageStart, 176⟩)
    (later : ∀ pool, messageStart + 176 ≤ plan.base pool) :
    TableState (resultState source (BitVec.ofNat 64 messageStart) recipient data length empty) kind plan slots cursor floor := by
  apply TableState.of_pool_frame (target := resultState source (BitVec.ofNat 64 messageStart) recipient data length empty) table rfl rfl rfl
  intro pool offset inside
  apply result_outside source.memory messageStart recipient data length empty _ region
  right
  rw [NaturalLayout.number kind plan table.valid pool offset (by omega)]
  have lower := later pool
  omega

end InitECandidate.Solver.GasBudget.Recipient

#print axioms InitECandidate.Solver.GasBudget.Recipient.condition_false
#print axioms InitECandidate.Solver.GasBudget.Recipient.noncreate_choice
#print axioms InitECandidate.Solver.GasBudget.Recipient.result_recipient
#print axioms InitECandidate.Solver.GasBudget.Recipient.result_table
