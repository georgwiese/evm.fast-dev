import InitECandidate.Solver.Mpt.AccountDestroyCall

namespace InitECandidate.Solver.Mpt.AccountCommit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_empty_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address scratch transaction empty : BitVec 64)
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
    (emptyLocal : source.locals.lookup (ofString "e") = some (.val (.word empty)))
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
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterEmpty = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (destroyed found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added ≤ 2 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (objects accountWriter).plan.capacity ≤
        (if destroyed then Get.bodyPrice (objects outer).kind (objects outer).slots.length + 3 +
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
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧ destroyed = decide (empty ≠ 0#64) ∧ (if destroyed then 1 ≤ added else added = 0 ∧ found = false ∧ iterations = 0) := by
  have dispatch := empty_dispatch source empty emptyLocal
  by_cases zero : empty = 0#64
  · rw [if_pos zero] at dispatch
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
    exact ⟨answerEq,false,false,0,0,cursor,objects,entries,0,by omega,by simp [emptyLocalsHOLFinite],Nat.le_refl _,by decide,by simpa using countBound,
      models,nextImage,zone,by simp,rfl,environment.of_fields rfl rfl rfl,(by intro key notHeap notCounter; rfl),values,savedValues,nextRegistry,
      Journal.CounterEffect.unchanged source target rfl,TableFamily.Metadata.refl objects,(fun query above earlier outside away => ⟨outside,rfl⟩),
      (fun table notWriter notOuter notAccount => rfl),Or.inl ⟨rfl,rfl⟩,counter,by simp [zero],by simp⟩
  · rw [if_neg zero] at dispatch
    rw [dispatch] at normal
    have safe : Input.LocalPrefix (ofString "addr") destroyCall := .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨mutated,destroyRun,returnRun,keepAddress⟩ := safe.normal_continue source post (.return (.const 0#64)) returned normal
    have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "addr"] = some [.val (.word address)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressLocal]
    obtain ⟨found,iterations,paid,nextCursor,next,nextEntries,added,positive,funded,clock,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,price,locals,codes,
      nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter⟩ := destroy_call_normal source mutated address scratch transaction cursor cutoff objects writer outer accountWriter base cap count entries
        family image zone countBound environment installed accounts registry property values owned accountOwned savedValues writerKind outerKind accountKind differentOuter
        addressArena scratchArena floors scratchBelow small journalAbove innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableBefore tableOutside outerMapped outerStored
        accountMapped accountStored accountAbove accountBefore accountOutside accountAway accountApart journal capacity counter _ args destroyRun
    have returnInfo := Input.return_normal mutated post (.const 0#64) returned returnRun
    have answerEq : returned = .val (.word 0#64) := Option.some.inj (returnInfo.1.symm.trans rfl)
    rw [returnInfo.2]
    let finish := emptyLocalsHOLFinite mutated
    have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
    have finalImage : Journal.Image finish next base (count + added) nextEntries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
    have finalRegistry := nextRegistry.framed mutated finish cutoff nextCursor nextCursor next next accounts
      (TableFamily.PersistentFrame.of_memory cutoff nextCursor next mutated finish rfl) (Nat.le_refl _) rfl
    refine ⟨answerEq,true,found,iterations,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,finalFamily,finalImage,nextZone,?_,codes,
      nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,nextSaved,finalRegistry,effect,metadata,?_,others,branch,nextCounter,by simp [zero],addedPositive⟩
    · simp only [Bool.true_eq,↓reduceIte]
      omega
    · intro query above earlier outside away
      exact frame query above earlier outside away

end InitECandidate.Solver.Mpt.AccountCommit

#print axioms InitECandidate.Solver.Mpt.AccountCommit.after_empty_normal
