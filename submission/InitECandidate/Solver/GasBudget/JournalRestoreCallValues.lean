import InitECandidate.Solver.GasBudget.JournalRestoreNormalValues
import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Actual original state_restore caller. The real journal counter supplies
the iteration count; the actual normal call supplies all clock funding. -/
theorem restore_call_normal_values {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count snap population : Nat) (entries : Nat → Entry ι) (ordered : snap ≤ count) (small : count < 2 ^ 64)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : EntryValues entries count property)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (code : source.code.lookup (ofString "state_restore") = some (formals, body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (BitVec.ofNat 64 snap))])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "state_restore") arguments) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      1 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base snap entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price population (count - snap) + 1 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + (count - snap)) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 snap))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ TableFamily.FloorFrame objects next source target ∧
      TableFamily.PersistentFrame 0 cursor objects next source target ∧ TableFamily.ValuesHave target next property ∧ EntryValues entries snap property ∧ TableFamily.Metadata objects next := by
  obtain ⟨callee, called, snapshot⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "state_restore") "snap" body (BitVec.ofNat 64 snap) code
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "state_restore") arguments _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects :=
    ⟨fun table => (family.tables table).of_fields rfl rfl rfl rfl, family.apart⟩
  have entryImage : Image entry objects base count entries :=
    image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  obtain ⟨returnedEq, paid, nextCursor, next, fits, clock, forward, models, nextImage, nextZone, bounded, nextPopulations, nextCounter,
    codes, nextEnvironment, globals, floorFrame, persistent, nextValues, nextSaved, pointers⟩ :=
    restore_body_normal_values entry post cursor objects base cap count snap population entries ordered small entryFamily entryImage zone countBound populations
      (environment.of_fields rfl rfl rfl) property values savedValues deleteCode journal counter snapshot returned bodyRun
  rw [returnedEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "state_restore") arguments _ body callee .one
    (.val (.word 0#64)) post args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have targetEq := congrArg Prod.snd (normal.symm.trans actual)
  change target = {post with locals := source.locals} at targetEq
  subst target
  have finalFamily : TableFamily.Model {post with locals := source.locals} nextCursor next :=
    ⟨fun table => (models.tables table).of_fields rfl rfl rfl rfl, models.apart⟩
  have finalImage : Image {post with locals := source.locals} next base snap entries :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  change paid ≤ source.clock - 1 at fits
  change post.clock = source.clock - 1 - paid at clock
  exact ⟨1 + paid, nextCursor, next, by omega, by omega, by change post.clock = _; omega, forward, finalFamily, finalImage, nextZone,
    by omega, nextPopulations, nextCounter, rfl, codes, nextEnvironment.of_fields rfl rfl rfl, globals, ⟨floorFrame.floors, floorFrame.words⟩,⟨persistent.words⟩,nextValues,nextSaved,pointers⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.restore_call_normal_values
