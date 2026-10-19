import InitECandidate.Solver.GasBudget.JournalAppendSetValues
import InitECandidate.Solver.GasBudget.JournalCounterLedger

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Real original jset caller establishes the next actual journal prefix,
retains all table owners/unused slots and charges the original setter growth
potential. Its source-clock allowance follows from normal execution. -/
theorem set_call_normal_values {ι : Type} [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (query value : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer value)
    (savedValues : EntryValues entries count property)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (code : source.code.lookup (ofString "jset") = some (TableCall.formals, setBody, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableCall.values (objects writer).pointer query value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "jset") arguments) = (none, target)) :
    count < cap ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (oldFlag oldValue : BitVec 64),
      1 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = (objects writer).kind ∧
      (oldFlag = 0#64 ∨ oldFlag = 1#64) ∧
      TableFamily.Model target nextCursor (Function.update objects writer next) ∧
      Image target (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, oldFlag, oldValue⟩) ∧
      Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        setPrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ CounterEffect source target 1 0 0 ∧ ProtectedFrame base cap cursor objects (Function.update objects writer next) source target ∧
      TableFamily.ValuesHave target (Function.update objects writer next) property ∧
      EntryValues (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,oldFlag,oldValue⟩) (count+1) property ∧ TableFamily.Metadata objects (Function.update objects writer next) := by
  obtain ⟨callee, called, t, key, v⟩ := TableCall.environment source.code.lookup (ofString "jset") setBody (objects writer).pointer query value code
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "jset") arguments _ setBody callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects :=
    ⟨fun index => (family.tables index).of_fields rfl rfl rfl rfl, family.apart⟩
  have entryImage : Image entry objects base count entries :=
    image.transfer (target := entry) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  obtain ⟨room, returnedEq, paid, nextCursor, next, flag, oldValue, fits, clock, forward, kind, binary, models, nextImage, nextZone, bounded, population,
    nextCounter, codes, nextEnvironment, globals, frame, finalValues, finalSaved, pointers⟩ :=
    set_body_normal_values entry post cursor objects writer base cap count entries entryFamily entryImage zone countBound (environment.of_fields rfl rfl rfl)
      query value property values owned savedValues queryFits queryMapped t key v getCode journal capacity counter returned bodyRun
  rw [returnedEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "jset") arguments _ setBody callee .one
    (.val (.word 0#64)) post args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {post with locals := source.locals} at same
  subst target
  have finalFamily : TableFamily.Model {post with locals := source.locals} nextCursor (Function.update objects writer next) :=
    ⟨fun index => (models.tables index).of_fields rfl rfl rfl rfl, models.apart⟩
  have finalImage : Image {post with locals := source.locals} (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, flag, oldValue⟩) :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  change paid ≤ source.clock - 1 at fits
  change post.clock = source.clock - 1 - paid at clock
  have countSmall : count + 1 < 2 ^ 64 := by
    have upper := zone.valid.upper
    change base + 32 * cap ≤ 33806089496 at upper
    omega
  have effect := CounterEffect.append source {post with locals := source.locals} count countSmall counter nextCounter
  exact ⟨room, 1 + paid, nextCursor, next, flag, oldValue, by omega, by omega, by change post.clock = _; omega, forward, kind, binary,
    finalFamily, finalImage, nextZone, by omega, population, nextCounter, rfl, codes, nextEnvironment.of_fields rfl rfl rfl, globals, effect,⟨frame.words⟩,finalValues,finalSaved,pointers⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_call_normal_values
