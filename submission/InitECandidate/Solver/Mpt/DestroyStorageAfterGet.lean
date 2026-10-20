import InitECandidate.Solver.Mpt.DestroyStorageEntry

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_get_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address scratch transaction flag value : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer outer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (outerKind : (objects outer).kind = .account)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (pairLocal : source.locals.lookup (ofString "m") = some (Get.pair flag value))
    (binary : flag = 0#64 ∨ flag = 1#64) (valueOwned : flag = 0#64 ∨ property outer value)
    (innerReferences : ∀ item, property outer item → ∃ reader, (objects reader).pointer = item ∧ (objects reader).kind = .word)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerLocal : source.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)))
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterGet = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added ≤ 1 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        (if found then loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
          GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → next table = objects table) ∧
      ((found = false ∧ iterations = 0 ∧ added = 0 ∧ next = objects ∧ nextEntries = entries) ∨
        (found = true ∧ ∃ reader, (objects reader).kind = .word ∧ iterations = (objects reader).slots.length)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧ (next outer).plan = (objects outer).plan := by
  have dispatch := after_get_dispatch source flag value pairLocal
  by_cases absent : flag = 0#64
  · rw [if_pos absent] at dispatch
    have same := normal.symm.trans dispatch
    have answerEq : returned = .val (.word 0#64) := by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst same
    have postEq := congrArg Prod.snd same
    change post = emptyLocalsHOLFinite source at postEq
    subst post
    let target := emptyLocalsHOLFinite source
    have models : TableFamily.Model target cursor objects := family.of_control rfl rfl rfl rfl
    have nextImage : Journal.Image target objects base (count + 0) entries :=
      image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
    have nextRegistry := registry.framed source target cutoff cursor cursor objects objects accounts
      (TableFamily.PersistentFrame.of_memory cutoff cursor objects source target rfl) (Nat.le_refl _) rfl
    exact ⟨answerEq,false,0,0,cursor,objects,entries,0,by omega,by simp [emptyLocalsHOLFinite],Nat.le_refl _,by decide,by simpa using countBound,
      models,nextImage,zone,by simp,rfl,environment.of_fields rfl rfl rfl,(by intro key notHeap notCounter; rfl),values,savedValues,nextRegistry,
      Journal.CounterEffect.unchanged source target rfl,TableFamily.Metadata.refl objects,(fun query above earlier outside away => ⟨outside,rfl⟩),
      (fun table notWriter notOuter => rfl),Or.inl ⟨rfl,rfl,rfl,rfl,rfl⟩,counter,rfl⟩
  · rw [if_neg absent] at dispatch
    rw [dispatch] at normal
    have presentFlag := binary.resolve_left absent
    obtain ⟨reader,pointer,readerKind⟩ := innerReferences value (valueOwned.resolve_left absent)
    have presentPair : source.locals.lookup (ofString "m") = some (Get.pair 1#64 (objects reader).pointer) := by
      rw [presentFlag,← pointer] at pairLocal
      exact pairLocal
    obtain ⟨answerEq,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,price,codes,nextEnvironment,globals,
      nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,nextCounter,outerPlan⟩ := present_normal source post address scratch transaction cursor cutoff objects writer reader outer base cap count entries
        family image zone countBound environment installed accounts registry property values owned savedValues writerKind readerKind outerKind addressArena scratchArena
        floors scratchBelow small journalAbove addressLocal presentPair scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableBefore tableOutside
        outerLocal accountApart journal capacity counter returned normal
    exact ⟨answerEq,true,(objects reader).slots.length,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,
      by simpa using price,codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,Or.inr ⟨rfl,reader,readerKind,rfl⟩,nextCounter,outerPlan⟩

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.after_get_normal
