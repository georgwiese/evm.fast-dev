import InitECandidate.Solver.Mpt.StorageSetResult

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_get_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address query flag value : BitVec 64) (words : Input.RlpWrite.U256Value.Words)
    (cursor cutoff population : Nat) (objects : ι → TableFamily.Object) (outer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (populations : ∀ reader,(objects reader).slots.length ≤ population)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (references : ∀ value,property outer value → ∃ reader,(objects reader).pointer = value ∧ (objects reader).kind = .word)
    (freshOwned : ∀ reader,(objects reader).kind = .word → ∀ pointer,AllocatedBytes.Arena pointer 32 → pointer.toNat % 8 = 0 → property reader pointer)
    (outerKind : (objects outer).kind = .account) (addressArena : AllocatedBytes.Arena address 20) (queryArena : AllocatedBytes.Arena query 32)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (queryLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (outerLocal : source.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)))
    (pairLocal : source.locals.lookup (ofString "m") = some (Get.pair flag value)) (owned : flag = 0#64 ∨ property outer value)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterGet = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ Result source post cursor cutoff population objects outer base cap count accounts property (tailPrice population) := by
  classical
  by_cases absent : flag = 0#64
  · subst flag
    obtain ⟨answerEq,room,paid,nextCursor,next,nextEntries,funded,clock,forward,models,nextImage,nextZone,price,outerCount,innerCount,codes,nextEnvironment,globals,
      nextValues,nextSaved,nextRegistry,effect,frame,metadata,nextCounter,others⟩ := absent_normal source post address query words cursor cutoff objects outer base cap count entries family image zone countBound environment installed
        accounts registry accountApart property values savedValues outerKind addressArena queryArena addressLocal queryLocal valueLocal outerLocal value pairLocal journal capacity counter returned normal
    have outerNextKind : (next (some outer)).kind = (objects outer).kind := metadata.kinds (some outer)
    have innerNextKind : (next none).kind = .word := metadata.kinds none
    have balance := TableFamily.potential_option_balance objects next outer others
    have oldPotential : (objects outer).potential = GrowRuntime.growthPotential (objects outer).kind (objects outer).plan.capacity := rfl
    have outerPotential : (next (some outer)).potential = GrowRuntime.growthPotential (objects outer).kind (next (some outer)).plan.capacity := by
      rw [TableFamily.Object.potential,outerNextKind]
    have innerPotential : (next none).potential = GrowRuntime.growthPotential .word (next none).plan.capacity := by
      rw [TableFamily.Object.potential,innerNextKind]
    rw [oldPotential,outerPotential,innerPotential] at balance
    rw [outerKind] at price
    have mono := set_price_mono .account (objects outer).slots.length population (populations outer)
    have amortized : paid + TableFamily.potential objects ≤ tailPrice population true + TableFamily.potential next := by
      unfold tailPrice
      simp only [↓reduceIte]
      rw [outerKind] at balance
      omega
    refine ⟨answerEq,Option ι,inferInstance,Option.some,next,newProperty property outer cursor,paid,nextCursor,2,true,nextEntries,
      Option.some_injective ι,by simp,funded,clock,forward,rfl,room,models,nextImage,nextZone,amortized,?_,codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,(fun query above earlier outside away => frame query earlier outside away),?_,nextCounter,?_,?_,?_⟩
    · intro reader
      cases reader with
      | none => omega
      | some reader =>
        by_cases same : reader = outer
        · subst reader; have before := populations outer; omega
        · rw [others reader same]; have before := populations reader; omega
    · intro reader
      exact ⟨metadata.kinds (some reader),metadata.floors (some reader),metadata.pointers (some reader)⟩
    · intro reader item prior
      exact Or.inl prior
    · intro reader other item
      simp [newProperty,TableNewOwnership.liftProperty,other]
    · intro item present
      rcases present with old | fresh
      · obtain ⟨reader,pointer,kind⟩ := references item old
        exact ⟨some reader,(metadata.pointers (some reader)).trans pointer,(metadata.kinds (some reader)).trans kind⟩
      · have pointer : (next none).pointer = BitVec.ofNat 64 cursor := metadata.pointers none
        exact ⟨none,pointer.trans fresh.2.symm,innerNextKind⟩
  · have presentOwned : property outer value := owned.resolve_left absent
    obtain ⟨writer,pointer,writerKind⟩ := references value presentOwned
    have pairRead : source.locals.lookup (ofString "m") = some (Get.pair flag (objects writer).pointer) := by rw [pointer]; exact pairLocal
    obtain ⟨room,answerEq,paid,nextCursor,next,oldFlag,oldValue,funded,clock,forward,models,nextImage,nextZone,price,populationBound,codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,frame,metadata,nextCounter⟩ :=
      present_normal source post query words cursor cutoff objects writer base cap count entries family image zone countBound environment installed accounts registry accountApart property values savedValues
        (freshOwned writer writerKind) writerKind queryArena queryLocal valueLocal flag absent pairRead journal capacity counter returned normal
    let nextObjects := Function.update objects writer next
    let nextEntries := Function.update entries count ⟨writer,BitVec.ofNat 64 (cursor + 32),oldFlag,oldValue⟩
    have nextKind : next.kind = (objects writer).kind := by simpa only [Function.update_self] using metadata.kinds writer
    have localPrice : paid + (objects writer).potential ≤ (Journal.Append.setPrice .word (objects writer).slots.length + 2) + next.potential := by
      simpa only [TableFamily.Object.potential,nextKind,writerKind] using price
    have globalPrice := TableFamily.amortized_update objects writer next paid (Journal.Append.setPrice .word (objects writer).slots.length + 2) localPrice
    change paid + TableFamily.potential objects ≤ (Journal.Append.setPrice .word (objects writer).slots.length + 2) + TableFamily.potential nextObjects at globalPrice
    have mono := set_price_mono .word (objects writer).slots.length population (populations writer)
    have amortized : paid + TableFamily.potential objects ≤ tailPrice population false + TableFamily.potential nextObjects := by
      simp only [tailPrice,Bool.false_eq_true,if_false]
      omega
    refine ⟨answerEq,ι,inferInstance,id,nextObjects,property,paid,nextCursor,1,false,nextEntries,fun _ _ same => same,by omega,funded,clock,by omega,rfl,by omega,
      models,nextImage,nextZone,amortized,TableFamily.population_update objects writer next population populations populationBound,codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,
      (fun query above earlier outside away => frame.words query earlier outside away),?_,nextCounter,fun _ _ prior => prior,fun _ _ _ => Iff.rfl,?_⟩
    · intro reader
      exact ⟨metadata.kinds reader,metadata.floors reader,metadata.pointers reader⟩
    · intro item prior
      obtain ⟨reader,pointer,kind⟩ := references item prior
      exact ⟨reader,(metadata.pointers reader).trans pointer,(metadata.kinds reader).trans kind⟩

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.after_get_normal
