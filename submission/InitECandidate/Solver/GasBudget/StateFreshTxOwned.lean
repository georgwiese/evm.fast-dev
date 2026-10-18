import InitECandidate.Solver.GasBudget.StateFreshTxNormal
import InitECandidate.Solver.GasBudget.StateFreshTxScopedOwned

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

def promoteEntry {ι : Type} (count : Nat) (entry : Journal.Entry ι) : Journal.Entry (Added count ι) :=
  ⟨embed count entry.writer, entry.key, entry.flag, entry.value⟩

/-- Complete original transaction-state initialization, including its actual
pointer fields, all older/new empty table models, journal reset and complete
unused reservation. No future room, constructor results or clock allowance
are assumed. Incoming ownership and installed original code remain explicit. -/
theorem owned_normal {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start : Nat) (objects : ι → TableFamily.Object) (base cap : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source start objects) (zone : Journal.Zone objects base cap start)
    (environment : WarmKeys.Environment source) (lower : 2701131776 ≤ start)
    (bounded : start ≤ 33806089496) (aligned : start % 8 = 0) (oldTs bs : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (ts : source.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (blockState : source.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧ 81 ≤ source.clock ∧ target.clock = source.clock - 81 ∧ target = resultState source start bs ∧
      start + 17176 ≤ 33806089496 ∧
      TableFamily.Model target (start + 17176) (objectsAfter objects (start + 72) (first :: rest)) ∧
      Journal.Zone (objectsAfter objects (start + 72) (first :: rest)) base cap (start + 17176) ∧
      Journal.Image target (objectsAfter objects (start + 72) (first :: rest)) base 0 (fun index => promoteEntry 8 (entries index)) ∧
      Fields target start (objectsAfter objects (start + 72) (first :: rest)) (first :: rest) ∧
      target.memory (MemoryRegion.address ⟨start, 72⟩ 0) = .word bs ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) ∧
      target.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 start))) ∧
      target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 17176)))) ∧
      WarmKeys.Environment target := by
  obtain ⟨returnedEq, funded, targetEq, clockEq, room, finalAligned, finalHeap, finalTs, finalEnvironment, globals⟩ :=
    body_normal source target start oldTs bs environment lower bounded aligned heap ts blockState newCode returned normal
  have prefixRoom : start + 72 ≤ 33806089496 := by omega
  have prefixAligned : (start + 72) % 8 = 0 := by omega
  have recordValid : MemoryRegion.Valid ⟨start, 72⟩ := ⟨lower, prefixRoom, aligned⟩
  have allocatedHeap : (allocatedState source start).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 72)))) := by
    have different : ofString "ts" ≠ ofString "heap_ptr" := by decide
    simp [allocatedState, Input.putGlobal, HolFiniteMapExact.update, FUPDATE, different]
  have advanced : TableFamily.Model (allocatedState source start) (start + 72) objects :=
    family.advance_cursor allocatedHeap (by omega) prefixRoom prefixAligned rfl rfl rfl
  have apart : TableFamily.ApartRegion objects ⟨start, 72⟩ := family.before_region _ (Nat.le_refl _)
  have enteredFamily : TableFamily.Model (blockStateStored source start bs) (start + 72) objects :=
    advanced.write_region ⟨start, 72⟩ recordValid apart 0 (by change 0 < 72; decide) bs
  have enteredZone : Journal.Zone objects base cap (start + 72) := zone.advance (by omega)
  have finalRoom : cursor (start + 72) (first :: rest) ≤ 33806089496 := by rw [cursor_all]; exact room
  obtain ⟨allTables, allZone, allApart, fields, savedBs⟩ := scoped_owned first rest (blockStateStored source start bs)
    (start + 72) start objects base cap entries enteredFamily enteredZone recordValid apart (Nat.le_refl _)
    (environment.of_fields rfl rfl rfl) (by omega) prefixAligned specs_valid offsets_distinct finalRoom
  rw [cursor_all] at allTables allZone
  have resultBs : (resultState source start bs).memory (MemoryRegion.address ⟨start, 72⟩ 0) = .word bs :=
    savedBs.trans (by simp [blockStateStored, StoreWord.put])
  have resultCounter : (resultState source start bs).globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) :=
    scoped_counter first rest _ _ _
  refine ⟨returnedEq, funded, clockEq, targetEq, room, ?_, allZone, Journal.Image.empty _ _ _ _, ?_, ?_, ?_, finalTs, finalHeap, finalEnvironment⟩
  · rw [targetEq]
    exact allTables
  · rw [targetEq]
    exact fields
  · rw [targetEq]
    exact resultBs
  · rw [targetEq]
    exact resultCounter

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.owned_normal
