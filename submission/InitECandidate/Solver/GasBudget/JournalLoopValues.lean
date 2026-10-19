import InitECandidate.Solver.GasBudget.JournalStepValues
import InitECandidate.Solver.GasBudget.JournalRestoreDefs

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Whole original rollback loop. The actual unsigned journal counter derives
the iteration count. Every iteration retains all remaining physical records
and live tables; growth potential telescopes across different writers. -/
theorem loop_normal_values {ι : Type} [Fintype ι] [DecidableEq ι] (remaining : Nat)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count snap population : Nat) (entries : Nat → Entry ι)
    (countEq : count = snap + remaining) (small : count < 2 ^ 64)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : EntryValues entries count property)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (snapshot : source.locals.lookup (ofString "snap") = some (.val (.word (BitVec.ofNat 64 snap))))
    (normal : evaluateHOLFiniteState source loop = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base snap entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price population remaining + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + remaining) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 snap))) ∧
      target.locals.lookup (ofString "snap") = some (.val (.word (BitVec.ofNat 64 snap))) ∧
      target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ TableFamily.FloorFrame objects next source target ∧
      TableFamily.PersistentFrame 0 cursor objects next source target ∧ TableFamily.ValuesHave target next property ∧ EntryValues entries snap property := by
  induction remaining generalizing source cursor objects count population with
  | zero =>
    have finished : count = snap := by omega
    have test := condition_read source (BitVec.ofNat 64 snap) (BitVec.ofNat 64 count) snapshot counter
    rw [finished, if_neg (by omega)] at test
    have actual : evaluateHOLFiniteState source loop = (none, source) := by
      simp only [eval, evalHOLFinite] at test
      rw [loop, evaluateHOLFiniteState_while_total]
      simp only [evalHOLFinite, test]
      simp
    have same := congrArg Prod.snd (normal.symm.trans actual)
    change target = source at same
    subst target
    refine ⟨0, cursor, objects, by omega, by simp, Nat.le_refl _, family, ?_, zone, by simp [price, WitnessBuild.triangle], ?_, ?_, snapshot, rfl,
      environment, OtherGlobals.refl source, TableFamily.FloorFrame.refl objects source,TableFamily.PersistentFrame.refl 0 cursor objects source,values,?_⟩
    · simpa only [finished] using image
    · simpa only [Nat.add_zero] using populations
    · simpa only [finished] using counter
    · simpa only [finished] using savedValues
  | succ remaining ih =>
    have active : snap < count := by omega
    have snapSmall : snap < 2 ^ 64 := by omega
    have test := condition_read source (BitVec.ofNat 64 snap) (BitVec.ofNat 64 count) snapshot counter
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt snapSmall, Nat.mod_eq_of_lt small, if_pos active] at test
    obtain ⟨positive, middle, bodyRun, tailRun, clockBound⟩ :=
      Input.while_none_step source target (ofString "snap") condition loopBody body_safe test normal
    let entry := decClockHOLFinite source
    have entryFamily : TableFamily.Model entry cursor objects :=
      ⟨fun table => (family.tables table).of_fields rfl rfl rfl rfl, family.apart⟩
    have entryImage : Image entry objects base count entries :=
      image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
    have entryEnvironment : WarmKeys.Environment entry := environment.of_fields rfl rfl rfl
    obtain ⟨paid, middleCursor, middleObjects, fits, clock, forward, middleFamily, middleImage, middleZone, bounded, middlePopulations,
      middleCounter, codes, middleEnvironment, globals, bodyFrame, bodyPersistent, middleValues, middleSaved⟩ :=
      body_normal_values entry middle cursor objects base cap count population entries entryFamily entryImage zone countBound (by omega) populations entryEnvironment property values savedValues deleteCode journal counter bodyRun
    have info := body_safe.summary entry
    rw [bodyRun] at info
    have middleSnapshot : middle.locals.lookup (ofString "snap") = some (.val (.word (BitVec.ofNat 64 snap))) := (info.1 rfl).trans snapshot
    have middleJournal : middle.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))) :=
      (globals (ofString "journal") (by decide) (by decide)).trans journal
    have middleDelete : middle.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one) := by rw [codes]; exact deleteCode
    obtain ⟨restPaid, nextCursor, next, restFits, restClock, restForward, nextFamily, nextImage, nextZone, restBound, nextPopulations,
      nextCounter, nextSnapshot, finalCodes, nextEnvironment, finalGlobals, restFrame, restPersistent, finalValues, finalSaved⟩ :=
      ih (source := middle) (cursor := middleCursor) (objects := middleObjects) (count := count - 1) (population := population + 1)
        (by omega) (by omega) middleFamily middleImage middleZone (by omega) middlePopulations middleEnvironment middleValues middleSaved middleDelete middleJournal middleCounter middleSnapshot tailRun
    change paid ≤ source.clock - 1 at fits
    change middle.clock = source.clock - 1 - paid at clock
    have headFrame : TableFamily.FloorFrame objects middleObjects source middle := ⟨bodyFrame.floors, bodyFrame.words⟩
    have headPersistent : TableFamily.PersistentFrame 0 cursor objects middleObjects source middle := ⟨bodyPersistent.words⟩
    refine ⟨1 + paid + restPaid, nextCursor, next, by omega, by omega, by omega, nextFamily, nextImage, nextZone, ?_, ?_, nextCounter, nextSnapshot,
      finalCodes.trans codes, nextEnvironment, globals.trans finalGlobals, headFrame.trans restFrame,headPersistent.trans restPersistent forward,finalValues,finalSaved⟩
    · rw [price_step]
      omega
    · intro table
      have bound := nextPopulations table
      omega

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.loop_normal_values
