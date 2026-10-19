import InitECandidate.Solver.Mpt.AccountCommitAfterEmpty

namespace InitECandidate.Solver.Mpt.AccountCommit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem empty_prefix_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address account emptyHash scratch transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer outer accountWriter : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64) (accountOwned : property accountWriter 1#64) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (outerKind : (objects outer).kind = .account) (accountKind : (objects accountWriter).kind = .account) (differentOuter : accountWriter ≠ outer)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (accountLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
    (accountMember : account ∈ accounts)
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32)
    (innerReferences : ∀ item, property outer item → ∃ reader, (objects reader).pointer = item ∧ (objects reader).kind = .word)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64))
    (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (accountMapped : source.memaddrs (transaction + 16#64))
    (accountStored : source.memory (transaction + 16#64) = .word (objects accountWriter).pointer)
    (accountAbove : cutoff ≤ (transaction + 16#64).toNat) (accountBefore : (transaction + 16#64).toNat < cursor)
    (accountOutside : TableFamily.Outside objects (transaction + 16#64)) (accountAway : Journal.Away base cap (transaction + 16#64))
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (.decCall (ofString "e") .one (ofString "acct_is_empty") [localVar "a"] afterEmpty) = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (empty : BitVec 64) (destroyed found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added ≤ 2 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (objects accountWriter).plan.capacity ≤
        7 + (if destroyed then Get.bodyPrice (objects outer).kind (objects outer).slots.length + 3 +
          (if found then DestroyStorage.loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
          Journal.Append.setPrice (objects accountWriter).kind (objects accountWriter).slots.length + 2 else 0) +
          GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (next accountWriter).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → table ≠ accountWriter → next table = objects table) ∧
      ((found = false ∧ iterations = 0) ∨
        (found = true ∧ ∃ reader, (objects reader).kind = .word ∧ iterations = (objects reader).slots.length)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧ destroyed = decide (empty ≠ 0#64) ∧ (empty = 0#64 ∨ empty = 1#64) ∧ (if destroyed then 1 ≤ added else added = 0 ∧ found = false ∧ iterations = 0) := by
  obtain ⟨accountImage⟩ := registry.images account accountMember
  have read : eval source (localVar "a") = some (.val (.word account)) := by simp [eval,localVar,evalHOLExact,toExact,accountLocal]
  obtain ⟨emptyPaid,empty,inner,emptyPositive,emptyBound,emptyFunded,binary,tailRun,scope⟩ := AccountIsEmpty.success_prefix source post account emptyHash accountImage
    emptyGlobal emptyArena installed "e" (localVar "a") afterEmpty read (some (.returned returned)) (Or.inr ⟨returned,rfl⟩) normal
  let ready := bind {source with clock := source.clock - emptyPaid} "e" empty
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) :=
    (bind_lookup_other _ "e" "addr" empty (by decide)).trans addressLocal
  have emptyLocal : ready.locals.lookup (ofString "e") = some (.val (.word empty)) := bind_lookup_same _ _ _
  obtain ⟨answerEq,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,price,codes,
    nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter,decision,appends⟩ := after_empty_normal ready inner address scratch transaction empty cursor cutoff objects writer outer accountWriter base cap count entries
      readyFamily readyImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts readyRegistry property values owned accountOwned savedValues writerKind outerKind accountKind differentOuter
      addressArena scratchArena floors scratchBelow small journalAbove readyAddress emptyLocal innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableBefore tableOutside
      outerMapped outerStored accountMapped accountStored accountAbove accountBefore accountOutside accountAway accountApart journal capacity counter returned tailRun
  rw [scope]
  let finish := restore source "e" inner
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + added) nextEntries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed inner finish cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next inner finish rfl) (Nat.le_refl _) rfl
  change paid ≤ source.clock - emptyPaid at funded
  change inner.clock = source.clock - emptyPaid - paid at clock
  have totalClock : inner.clock = source.clock - (emptyPaid + paid) := by rw [clock,Nat.sub_sub]
  have totalFunded : emptyPaid + paid ≤ source.clock := by
    calc
      emptyPaid + paid ≤ emptyPaid + (source.clock - emptyPaid) := Nat.add_le_add_left funded emptyPaid
      _ = source.clock := Nat.add_sub_of_le emptyFunded
  refine ⟨answerEq,empty,destroyed,found,iterations,emptyPaid + paid,nextCursor,next,nextEntries,added,totalFunded,totalClock,forward,addedBound,capacityBound,finalFamily,finalImage,nextZone,by omega,
    codes,nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,nextSaved,finalRegistry,effect,metadata,?_,others,branch,nextCounter,decision,binary,appends⟩
  intro query above earlier outside away
  exact frame query above earlier outside away

end InitECandidate.Solver.Mpt.AccountCommit

#print axioms InitECandidate.Solver.Mpt.AccountCommit.empty_prefix_normal
