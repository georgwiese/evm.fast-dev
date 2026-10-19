import InitECandidate.Solver.Mpt.StorageSetNewNormal

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem absent_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address query : BitVec 64) (words : Input.RlpWrite.U256Value.Words)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (outer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (outerKind : (objects outer).kind = .account) (addressArena : AllocatedBytes.Arena address 20) (queryArena : AllocatedBytes.Arena query 32)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (queryLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (outerLocal : source.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)))
    (old : BitVec 64) (pairLocal : source.locals.lookup (ofString "m") = some (Get.pair 0#64 old))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterGet = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ count + 2 ≤ cap ∧ ∃ (paid nextCursor : Nat) (next : Option ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry (Option ι)),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + 2) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects outer).kind (objects outer).plan.capacity + GrowRuntime.growthPotential .word 8 ≤
        TableRuntime.price 8 + Journal.Append.setPrice (objects outer).kind (objects outer).slots.length + Journal.Append.setPrice .word 0 + 4 +
          GrowRuntime.growthPotential (objects outer).kind (next (some outer)).plan.capacity + GrowRuntime.growthPotential .word (next none).plan.capacity ∧
      (next (some outer)).slots.length ≤ (objects outer).slots.length + 1 ∧ (next none).slots.length ≤ 1 ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧
      TableFamily.ValuesHave post next (newProperty property outer cursor) ∧ Journal.EntryValues nextEntries (count + 2) (newProperty property outer cursor) ∧
      AccountDecode.Registry post cutoff nextCursor next accounts ∧ Journal.CounterEffect source post 2 0 0 ∧
      (∀ query : BitVec 64,query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query → TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      TableFamily.Metadata (TableFamily.extend objects (Journal.newObject .word cursor 8)) next ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 2)))) ∧
      (∀ reader,reader ≠ outer → next (some reader) = objects reader) := by
  have execute := absent_dispatch source old pairLocal
  rw [execute] at normal
  let ready := bind source "inner" 0#64
  let inner := (evaluateHOLFiniteState ready newBranch).2
  have resultEq := congrArg Prod.fst normal
  change (evaluateHOLFiniteState ready newBranch).1 = some (.returned returned) at resultEq
  have tailRun : evaluateHOLFiniteState ready newBranch = (some (.returned returned),inner) := Prod.ext resultEq rfl
  have scope := congrArg Prod.snd normal
  change restore source "inner" inner = post at scope
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) :=
    (bind_lookup_other source "inner" "addr" _ (by decide)).trans addressLocal
  have readyQuery : ready.locals.lookup (ofString "key") = some (.val (.word query)) :=
    (bind_lookup_other source "inner" "key" _ (by decide)).trans queryLocal
  have readyValue : ready.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words) :=
    (bind_lookup_other source "inner" "value" _ (by decide)).trans valueLocal
  have readyOuter : ready.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)) :=
    (bind_lookup_other source "inner" "outer" _ (by decide)).trans outerLocal
  obtain ⟨answerEq,room,paid,nextCursor,next,nextEntries,funded,clock,forward,models,nextImage,nextZone,price,outerCount,innerCount,codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,frame,metadata,nextCounter,others⟩ :=
    new_branch_normal ready inner address query words cursor cutoff objects outer base cap count entries readyFamily readyImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts readyRegistry accountApart property values savedValues
      outerKind addressArena queryArena readyAddress readyQuery readyValue readyOuter (bind_lookup_same _ _ _) journal capacity counter returned tailRun
  rw [← scope]
  let finish := restore source "inner" inner
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + 2) nextEntries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed inner finish cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next inner finish rfl) (Nat.le_refl _) rfl
  exact ⟨answerEq,room,paid,nextCursor,next,nextEntries,funded,clock,forward,finalFamily,finalImage,nextZone,price,outerCount,innerCount,codes,nextEnvironment.of_fields rfl rfl rfl,
    globals,nextValues,nextSaved,finalRegistry,effect,frame,metadata,nextCounter,others⟩

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.absent_normal
