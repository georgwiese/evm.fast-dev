import InitECandidate.Solver.GasBudget.JournalAppendDeleteValues
import InitECandidate.Solver.GasBudget.JournalCounterLedger

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

private theorem delete_environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (table key : BitVec 64)
    (code : codeFn (ofString "jdel") = some (Find.formals, deleteBody, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), lookupCodeHOLFinite codeFn (ofString "jdel") [.val (.word table), .val (.word key)] = some (deleteBody, callee, .one) ∧
      callee.lookup (ofString "t") = some (.val (.word table)) ∧ callee.lookup (ofString "key") = some (.val (.word key)) := by
  have valid : (Find.formals.map Prod.fst).Nodup ∧ Find.formals.length = ([.val (.word table), .val (.word key)] : List (ValueHOL 64)).length ∧
      ((Find.formals.zip [.val (.word table), .val (.word key)]).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    refine ⟨by decide, rfl, ?_⟩
    simp [Find.formals, shapeOfHOLExact, shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "jdel") [.val (.word table), .val (.word key)] = some (deleteBody, Find.rawLocals table key, .one) := by
    simp only [lookupCodeHOLExact, code, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee, called, ?_, ?_⟩
  all_goals rw [locals]
  · simp [Find.rawLocals, show ofString "t" ≠ ofString "key" from by decide]
  · simp [Find.rawLocals]

/-- The actual original jdel caller either changes only its paid clock, or
appends one real record and returns the complete family/image/reservation.
Both branches derive their clocks from the normal call, including its ABI. -/
theorem delete_call_normal_values {ι : Type} [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (query : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : EntryValues entries count property)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (code : source.code.lookup (ofString "jdel") = some (Find.formals, deleteBody, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (objects writer).pointer), .val (.word query)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "jdel") arguments) = (none, target)) :
    (∃ paid, 2 ≤ paid ∧ paid ≤ Get.bodyPrice (objects writer).kind (objects writer).slots.length + 2 ∧ paid ≤ source.clock ∧ target = {source with clock := source.clock - paid} ∧ CounterEffect source target 0 0 0) ∨
    (count < cap ∧ ∃ (paid : Nat) (next : TableFamily.Object) (oldValue : BitVec 64),
      2 ≤ paid ∧ paid ≤ deletePrice (objects writer).kind (objects writer).slots.length + 1 ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
      TableFamily.Model target (cursor + NaturalLayout.stride (objects writer).kind) (Function.update objects writer next) ∧
      Image target (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, 1#64, oldValue⟩) ∧
      Zone (Function.update objects writer next) base cap (cursor + NaturalLayout.stride (objects writer).kind) ∧
      next.slots.length ≤ (objects writer).slots.length ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ CounterEffect source target 1 0 0 ∧ ProtectedFrame base cap cursor objects (Function.update objects writer next) source target ∧
      TableFamily.ValuesHave target (Function.update objects writer next) property ∧
      EntryValues (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,1#64,oldValue⟩) (count+1) property ∧ TableFamily.Metadata objects (Function.update objects writer next)) := by
  obtain ⟨callee, called, t, key⟩ := delete_environment source.code.lookup (objects writer).pointer query code
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "jdel") arguments _ deleteBody callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects :=
    ⟨fun index => (family.tables index).of_fields rfl rfl rfl rfl, family.apart⟩
  have entryImage : Image entry objects base count entries :=
    image.transfer (target := entry) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  obtain ⟨returnedEq, branches⟩ := delete_body_normal_values entry post cursor objects writer base cap count entries entryFamily entryImage zone countBound
    (environment.of_fields rfl rfl rfl) query property values savedValues queryFits queryMapped t key getCode deleteCode journal capacity counter returned bodyRun
  rw [returnedEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "jdel") arguments _ deleteBody callee .one
    (.val (.word 0#64)) post args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {post with locals := source.locals} at same
  subst target
  rcases branches with absent | present
  · obtain ⟨paid, bodyPositive, bounded, fits, frame⟩ := absent
    have restored := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
    change {post with locals := source.locals} = {source with clock := source.clock - 1 - paid} at restored
    change paid ≤ source.clock - 1 at fits
    have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
    left
    exact ⟨paid + 1, by omega, by omega, by omega, by simpa only [subtract] using restored,
      CounterEffect.unchanged source _ (by rw [restored])⟩
  · obtain ⟨room, paid, next, oldValue, bodyPositive, bounded, fits, clock, kind, plan, models, nextImage, nextZone, population,
      nextCounter, codes, nextEnvironment, globals, frame, nextValues, nextSaved, pointers⟩ := present
    have finalFamily : TableFamily.Model {post with locals := source.locals} (cursor + NaturalLayout.stride (objects writer).kind) (Function.update objects writer next) :=
      ⟨fun index => (models.tables index).of_fields rfl rfl rfl rfl, models.apart⟩
    have finalImage : Image {post with locals := source.locals} (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, 1#64, oldValue⟩) :=
      nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
    change paid ≤ source.clock - 1 at fits
    change post.clock = source.clock - 1 - paid at clock
    have countSmall : count + 1 < 2 ^ 64 := by
      have upper := zone.valid.upper
      change base + 32 * cap ≤ 33806089496 at upper
      omega
    have effect := CounterEffect.append source {post with locals := source.locals} count countSmall counter nextCounter
    right
    exact ⟨room, paid + 1, next, oldValue, by omega, by omega, by omega, by change post.clock = _; omega, kind, plan,
      finalFamily, finalImage, nextZone, population, nextCounter, rfl, codes, nextEnvironment.of_fields rfl rfl rfl, globals, effect,⟨frame.words⟩,nextValues,nextSaved,pointers⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_call_normal_values
