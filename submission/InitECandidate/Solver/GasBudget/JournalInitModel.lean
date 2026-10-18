import InitECandidate.Solver.GasBudget.JournalInitFields
import InitECandidate.Solver.GasBudget.JournalSnapshot
import InitECandidate.Solver.GasBudget.JournalRecordGeometry
import InitECandidate.Solver.MutableTable.FamilyMemoryFrame

namespace InitECandidate.Solver.GasBudget.Journal.Initialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Actual initialization creates the complete unused reservation after all
existing table pools. Allocation does not need to clear journal records:
the initial live prefix is empty and its counter is the real written zero. -/
theorem owned_normal {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (objects : ι → TableFamily.Object) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (lower : 2701131776 ≤ cursor)
    (bounded : cursor ≤ 33806089496) (aligned : cursor % 8 = 0) (journalOld : BitVec 64)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word journalOld)))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source selected = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧ 1 ≤ source.clock ∧ cursor + bytes ≤ 33806089496 ∧ target.clock = source.clock - 1 ∧
      TableFamily.Model target (cursor + bytes) objects ∧ Zone objects cursor capacity (cursor + bytes) ∧ Image target objects cursor 0 entries ∧
      target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + bytes)))) ∧
      target.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 capacity))) ∧
      target.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 cursor))) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) ∧
      target.globals.lookup (ofString "ts") = some (.val (.word 0#64)) := by
  obtain ⟨returnedEq, room, positive, same⟩ := normal source target cursor journalOld bounded aligned journal heap allocCode trapCode returned run
  subst target
  have fields := globals source cursor
  have nextAligned : (cursor + bytes) % 8 = 0 := by rw [Nat.add_mod, aligned, show bytes % 8 = 0 from by decide]
  have nextFamily : TableFamily.Model (emptyLocalsHOLFinite (initialized source cursor)) (cursor + bytes) objects :=
    family.advance_cursor fields.1 (by omega) room nextAligned rfl rfl rfl
  have region : MemoryRegion.Valid ⟨cursor, 32 * capacity⟩ :=
    ⟨lower, by change cursor + 32 * capacity ≤ 33806089496; simpa only [bytes, Nat.mul_comm] using room, aligned⟩
  have zone : Zone objects cursor capacity (cursor + bytes) := by
    refine ⟨region, by dsimp only [bytes]; omega, ?_⟩
    intro index inside field table
    apply TableFootprint.Outside.of_regions (objects table).kind (objects table).plan (family.tables table).valid
    intro pool
    right
    rw [entry_number cursor capacity index field region inside]
    have before := (family.tables table).earlier pool
    omega
  exact ⟨returnedEq, positive, room, rfl, nextFamily, zone, Image.empty _ objects cursor entries, fields⟩

end InitECandidate.Solver.GasBudget.Journal.Initialization

#print axioms InitECandidate.Solver.GasBudget.Journal.Initialization.owned_normal
