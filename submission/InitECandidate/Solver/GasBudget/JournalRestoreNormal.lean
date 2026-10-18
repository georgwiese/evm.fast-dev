import InitECandidate.Solver.GasBudget.JournalLoop

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The complete original state_restore body, including its real zero
return. Current physical ownership is explicit; helper runs, clock funding
and the rollback trace are derived from the actual normal outcome. -/
theorem restore_body_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base count snap population : Nat) (entries : Nat → Entry ι) (ordered : snap ≤ count) (small : count < 2 ^ 64)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (extent : base + 32 * count ≤ cursor) (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (snapshot : source.locals.lookup (ofString "snap") = some (.val (.word (BitVec.ofNat 64 snap))))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base snap entries ∧
      paid + TableFamily.potential objects ≤ price population (count - snap) + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + (count - snap)) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 snap))) ∧
      target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target := by
  rw [body_shape] at normal
  obtain ⟨middle, loopRun, returnRun, saved⟩ :=
    (Input.LocalPrefix.loop condition body_safe).normal_continue source target (.return (.const 0#64)) returned normal
  have actual : evaluateHOLFiniteState middle (.return (.const 0#64)) = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite middle) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have returnedEq : returned = .val (.word 0#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst (returnRun.symm.trans actual)
  have targetEq := congrArg Prod.snd (returnRun.symm.trans actual)
  change target = emptyLocalsHOLFinite middle at targetEq
  obtain ⟨paid, nextCursor, next, fits, clock, forward, models, nextImage, bounded, nextPopulations, nextCounter, nextSnapshot,
    codes, nextEnvironment, globals⟩ :=
    loop_normal (count - snap) source middle cursor objects base count snap population entries (by omega) small family image extent populations environment deleteCode journal counter snapshot loopRun
  subst target
  have finalFamily : TableFamily.Model (emptyLocalsHOLFinite middle) nextCursor next :=
    ⟨fun table => (models.tables table).of_fields rfl rfl rfl rfl, models.apart⟩
  have finalImage : Image (emptyLocalsHOLFinite middle) next base snap entries :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  exact ⟨returnedEq, paid, nextCursor, next, fits, clock, forward, finalFamily, finalImage, bounded, nextPopulations, nextCounter,
    codes, nextEnvironment.of_fields rfl rfl rfl, globals⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.restore_body_normal
