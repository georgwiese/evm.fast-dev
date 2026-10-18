import InitECandidate.Solver.GasBudget.JournalRestoreCall

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- A snapshot at or beyond the current counter takes no rollback iteration.
This remains valid for high-bit words and needs no table or memory premises. -/
theorem inactive_body (source : PanSemStateFiniteExact 64 Guest.HostMemory) (snap count : BitVec 64)
    (snapshot : source.locals.lookup (ofString "snap") = some (.val (.word snap)))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (finished : count.toNat ≤ snap.toNat) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  have test := condition_read source snap count snapshot counter
  rw [if_neg (by omega)] at test
  have loopRun : evaluateHOLFiniteState source loop = (none, source) := by
    simp only [eval] at test
    rw [loop, evaluateHOLFiniteState_while_total]
    simp only [evalHOLFinite, test]
    simp
  rw [body_shape, WitnessRadix.StateSteps.next_sequence source source _ _ loopRun (Nat.le_refl _)]
  simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]

theorem inactive_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (snap count : BitVec 64)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (finished : count.toNat ≤ snap.toNat)
    (code : source.code.lookup (ofString "state_restore") = some (formals, body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word snap)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "state_restore") arguments) = (none, target)) :
    1 ≤ source.clock ∧ target = {source with clock := source.clock - 1} := by
  obtain ⟨callee, called, snapshot⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "state_restore") "snap" body snap code
  obtain ⟨positive, _, _, _⟩ := Input.CallNormal.ignored_callee_return source target (ofString "state_restore") arguments _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have bodyRun := inactive_body entry snap count snapshot counter finished
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "state_restore") arguments _ body callee .one
    (.val (.word 0#64)) (emptyLocalsHOLFinite entry) args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have same := congrArg Prod.snd (normal.symm.trans actual)
  exact ⟨positive, same⟩

/-- All snapshots are covered: an already-restored later snapshot is a real
no-op. Otherwise actual journal progress determines the precise loop count. -/
theorem restore_call_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count snap population : Nat) (entries : Nat → Entry ι) (countSmall : count < 2 ^ 64) (snapSmall : snap < 2 ^ 64)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (code : source.code.lookup (ofString "state_restore") = some (formals, body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (BitVec.ofNat 64 snap))])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "state_restore") arguments) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      1 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base (min count snap) entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price population (count - snap) + 1 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + (count - snap)) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (min count snap)))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ TableFamily.FloorFrame objects next source target := by
  by_cases ordered : snap ≤ count
  · simpa only [Nat.min_eq_right ordered] using restore_call_normal source target cursor objects base cap count snap population entries ordered countSmall family image zone countBound populations environment deleteCode code journal counter arguments args normal
  · have finished : count ≤ snap := by omega
    have wordFinished : (BitVec.ofNat 64 count).toNat ≤ (BitVec.ofNat 64 snap).toNat := by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countSmall, Nat.mod_eq_of_lt snapSmall]
      exact finished
    obtain ⟨positive, same⟩ := inactive_call_normal source target (BitVec.ofNat 64 snap) (BitVec.ofNat 64 count) counter wordFinished code arguments args normal
    subst target
    have nextFamily : TableFamily.Model {source with clock := source.clock - 1} cursor objects :=
      ⟨fun table => (family.tables table).of_fields rfl rfl rfl rfl, family.apart⟩
    have nextImage : Image {source with clock := source.clock - 1} objects base count entries :=
      image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
    rw [Nat.min_eq_left finished]
    exact ⟨1, cursor, objects, by omega, positive, rfl, Nat.le_refl _, nextFamily, nextImage, zone,
      by simp [price, WitnessBuild.triangle, Nat.sub_eq_zero_of_le finished],
      (by intro table; have bounded := populations table; omega), counter, rfl, rfl, environment.of_fields rfl rfl rfl, OtherGlobals.refl source, ⟨fun _ => rfl, fun _ _ => rfl⟩⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.inactive_body
#print axioms InitECandidate.Solver.GasBudget.Journal.inactive_call_normal
#print axioms InitECandidate.Solver.GasBudget.Journal.restore_call_bound
