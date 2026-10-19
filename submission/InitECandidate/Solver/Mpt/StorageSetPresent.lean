import InitECandidate.Solver.Mpt.StorageSetValue
import InitECandidate.Solver.Mpt.StorageSetDispatch

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem present_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (query : BitVec 64) (words : Input.RlpWrite.U256Value.Words)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (freshOwned : ∀ pointer,AllocatedBytes.Arena pointer 32 → pointer.toNat % 8 = 0 → property writer pointer)
    (writerKind : (objects writer).kind = .word) (queryArena : AllocatedBytes.Arena query 32)
    (queryLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (flag : BitVec 64) (present : flag ≠ 0#64)
    (pairLocal : source.locals.lookup (ofString "m") = some (Get.pair flag (objects writer).pointer))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterGet = (some (.returned returned),post)) :
    count < cap ∧ returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (oldFlag oldValue : BitVec 64),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor + 32 ≤ nextCursor ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Journal.Image post (Function.update objects writer next) base (count + 1)
        (Function.update entries count ⟨writer,BitVec.ofNat 64 (cursor + 32),oldFlag,oldValue⟩) ∧ Journal.Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Journal.Append.setPrice (objects writer).kind (objects writer).slots.length + 2 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧ post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧
      Journal.EntryValues (Function.update entries count ⟨writer,BitVec.ofNat 64 (cursor + 32),oldFlag,oldValue⟩) (count + 1) property ∧
      AccountDecode.Registry post cutoff nextCursor (Function.update objects writer next) accounts ∧ Journal.CounterEffect source post 1 0 0 ∧
      Journal.ProtectedFrame base cap cursor objects (Function.update objects writer next) source post ∧ TableFamily.Metadata objects (Function.update objects writer next) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) := by
  have execute := present_dispatch source flag (objects writer).pointer pairLocal present
  rw [execute] at normal
  let ready := bind source "inner" (objects writer).pointer
  let inner := (evaluateHOLFiniteState ready allocate).2
  have resultEq := congrArg Prod.fst normal
  change (evaluateHOLFiniteState ready allocate).1 = some (.returned returned) at resultEq
  have tailRun : evaluateHOLFiniteState ready allocate = (some (.returned returned),inner) := Prod.ext resultEq rfl
  have scope := congrArg Prod.snd normal
  change restore source "inner" inner = post at scope
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyQuery : ready.locals.lookup (ofString "key") = some (.val (.word query)) :=
    (bind_lookup_other source "inner" "key" _ (by decide)).trans queryLocal
  have readyValue : ready.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words) :=
    (bind_lookup_other source "inner" "value" _ (by decide)).trans valueLocal
  obtain ⟨room,answerEq,paid,nextCursor,next,oldFlag,oldValue,funded,clock,forward,models,nextImage,nextZone,price,population,codes,nextEnvironment,globals,
    nextValues,nextSaved,nextRegistry,effect,frame,metadata,nextCounter⟩ := allocate_tail_normal ready inner query words cursor cutoff objects writer base cap count entries
      readyFamily readyImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts readyRegistry accountApart property values savedValues freshOwned writerKind queryArena readyQuery readyValue
      (bind_lookup_same _ _ _) journal capacity counter returned tailRun
  rw [← scope]
  let finish := restore source "inner" inner
  have finalFamily : TableFamily.Model finish nextCursor (Function.update objects writer next) := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer,BitVec.ofNat 64 (cursor + 32),oldFlag,oldValue⟩) :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed inner finish cutoff nextCursor nextCursor (Function.update objects writer next) (Function.update objects writer next) accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor _ inner finish rfl) (Nat.le_refl _) rfl
  exact ⟨room,answerEq,paid,nextCursor,next,oldFlag,oldValue,funded,clock,forward,finalFamily,finalImage,nextZone,price,population,codes,nextEnvironment.of_fields rfl rfl rfl,
    globals,nextValues,nextSaved,finalRegistry,effect,⟨frame.words⟩,metadata,nextCounter⟩

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.present_normal
