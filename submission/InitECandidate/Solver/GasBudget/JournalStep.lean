import InitECandidate.Solver.GasBudget.JournalRecordsNormal

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def OtherGlobals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∀ key : MlS, key ≠ ofString "heap_ptr" → key ≠ ofString "journal_n" → target.globals.lookup key = source.globals.lookup key

theorem OtherGlobals.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) : OtherGlobals source source := by
  intro key heap counter
  rfl

theorem OtherGlobals.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (first : OtherGlobals source middle) (second : OtherGlobals middle target) : OtherGlobals source target := by
  intro key heap counter
  exact (second key heap counter).trans (first key heap counter)

/-- One complete actual original rollback body. The executed decrement and
record loads choose the writer; the helper preserves the new counter and all
remaining record images. No helper execution or iteration budget is assumed. -/
theorem body_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base count population : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (extent : base + 32 * count ≤ cursor) (positive : 0 < count)
    (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (normal : evaluateHOLFiniteState source loopBody = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base (count - 1) entries ∧
      paid + TableFamily.potential objects ≤ 38 * population + 39 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + 1) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count - 1)))) ∧
      target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target := by
  obtain ⟨middle, decrementRun, recordRun⟩ := Input.sequence_none source target decrement records normal
  have decrementActual := decrement_execute source (BitVec.ofNat 64 count) counter
  have middleEq := congrArg Prod.snd (decrementRun.symm.trans decrementActual)
  change middle = Input.putGlobal source "journal_n" (BitVec.ofNat 64 count - 1#64) at middleEq
  subst middle
  let entry := Input.putGlobal source "journal_n" (BitVec.ofNat 64 count - 1#64)
  have wordSub : BitVec.ofNat 64 count - 1#64 = BitVec.ofNat 64 (count - 1) :=
    BitVec.ofNat_sub_ofNat_of_le count 1 (by decide) (by omega)
  have entryFamily : TableFamily.Model entry cursor objects := decrement_family source cursor objects family (BitVec.ofNat 64 count)
  have entryImage : Image entry objects base count entries :=
    image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have entryEnvironment : WarmKeys.Environment entry := environment.of_fields rfl rfl rfl
  have entryJournal : entry.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))) :=
    (Input.putGlobal.lookup_other source "journal_n" _ (ofString "journal") (by decide)).trans journal
  have entryCounter : entry.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count - 1)))) := by
    change (Input.putGlobal source "journal_n" (BitVec.ofNat 64 count - 1#64)).globals.lookup _ = _
    rw [Input.putGlobal.lookup_same, wordSub]
  obtain ⟨paid, nextCursor, next, fits, clock, forward, nextFamily, nextImage, bounded, nextPopulations, codes, nextEnvironment, globals⟩ :=
    records_normal entry target cursor objects base count (count - 1) population entries entryFamily entryImage extent (by omega) populations
      entryEnvironment deleteCode entryJournal entryCounter recordRun
  refine ⟨paid, nextCursor, next, fits, clock, forward, nextFamily, nextImage.restrict (Nat.sub_le count 1), bounded, nextPopulations,
    (globals (ofString "journal_n") (by decide)).trans entryCounter, codes, nextEnvironment, ?_⟩
  intro key heap different
  exact (globals key heap).trans (Input.putGlobal.lookup_other source "journal_n" _ key different)

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.OtherGlobals.trans
#print axioms InitECandidate.Solver.GasBudget.Journal.body_normal
