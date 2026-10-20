import InitECandidate.Solver.Mpt.AccountBalanceMutationFamily

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem balance_commit_return_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address account emptyHash scratch transaction : BitVec 64)
    (cursor cutoff protectedCursor populationBound : Nat) (objects : ι → TableFamily.Object) (writer outer accountWriter : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (population : ∀ index,(objects index).slots.length ≤ populationBound)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64) (accountOwned : property accountWriter 1#64) (publishOwned : property accountWriter account) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (outerKind : (objects outer).kind = .account) (accountKind : (objects accountWriter).kind = .account) (differentOuter : accountWriter ≠ outer)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (accountMember : account ∈ accounts) (protectedBefore : protectedCursor ≤ account.toNat)
    (addressName accountName : String) (words : Input.RlpWrite.U256Value.Words) (expression : ExpHOL 64)
    (addressLocal : source.locals.lookup (ofString addressName) = some (.val (.word address)))
    (accountLocal : source.locals.lookup (ofString accountName) = some (.val (.word account)))
    (valueRead : eval source expression = some (Input.RlpWrite.U256Value.tuple words))
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32)
    (innerReferences : ∀ item, property outer item → ∃ reader, (objects reader).pointer = item ∧ (objects reader).kind = .word)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (tableAway : Journal.Away base cap (transaction + 24#64))
    (tableBefore : (transaction + 24#64).toNat < protectedCursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64))
    (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (outerBefore : (transaction + 32#64).toNat < protectedCursor)
    (outerOutside : TableFamily.Outside objects (transaction + 32#64)) (outerAway : Journal.Away base cap (transaction + 32#64))
    (accountMapped : source.memaddrs (transaction + 16#64))
    (accountStored : source.memory (transaction + 16#64) = .word (objects accountWriter).pointer)
    (accountAbove : cutoff ≤ (transaction + 16#64).toNat) (accountBefore : (transaction + 16#64).toNat < protectedCursor)
    (accountOutside : TableFamily.Outside objects (transaction + 16#64)) (accountAway : Journal.Away base cap (transaction + 16#64))
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (balanceCommit addressName accountName expression) (.return (.const 0#64))) = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (empty : BitVec 64) (destroyed found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      1 ≤ paid ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ 1 ≤ added ∧ added ≤ 3 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ commitPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length destroyed found iterations + TableFamily.potential next ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < protectedCursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → table ≠ accountWriter → next table = objects table) ∧
      ((found = false ∧ iterations = 0) ∨
        (found = true ∧ ∃ reader, (objects reader).kind = .word ∧ iterations = (objects reader).slots.length)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧ destroyed = decide (empty ≠ 0#64) ∧ (empty = 0#64 ∨ empty = 1#64) ∧ (if destroyed then 2 ≤ added else added = 1 ∧ found = false ∧ iterations = 0) ∧ (next outer).plan = (objects outer).plan ∧
      (next writer).slots.length ≤ (objects writer).slots.length + iterations ∧ (next outer).slots.length ≤ (objects outer).slots.length ∧ (next accountWriter).slots.length ≤ (objects accountWriter).slots.length + 2 ∧ iterations ≤ populationBound ∧ (∀ index,(next index).slots.length ≤ populationBound + iterations + 2) := by
  have safe : Input.LocalPrefix (ofString addressName) (balanceCommit addressName accountName expression) :=
    .seq (.store _ _) (.call none _ _ (by intro name impossible; cases impossible))
  obtain ⟨mutated,mutationRun,returnRun,keepAddress⟩ := safe.normal_continue source post (.return (.const 0#64)) returned normal
  obtain ⟨empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,positive,funded,clock,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,price,locals,codes,nextEnvironment,globals,
    nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan,markerPopulation,outerPopulation,accountPopulation,visits,populations⟩ := balance_commit_family_normal source mutated address account emptyHash scratch transaction
    cursor cutoff protectedCursor populationBound objects writer outer accountWriter base cap count entries population family image zone countBound environment installed accounts registry property values owned accountOwned publishOwned savedValues
    writerKind outerKind accountKind differentOuter addressArena scratchArena floors scratchBelow small journalAbove accountMember protectedBefore addressName accountName words expression addressLocal accountLocal valueRead
    emptyGlobal emptyArena innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableAway tableBefore tableOutside outerMapped outerStored outerBefore outerOutside outerAway accountMapped accountStored accountAbove accountBefore accountOutside accountAway accountApart journal capacity counter mutationRun
  have returnedInfo := Input.return_normal mutated post (.const 0#64) returned returnRun
  have answerEq : returned = .val (.word 0#64) := Option.some.inj (returnedInfo.1.symm.trans rfl)
  rw [returnedInfo.2]
  let finish := emptyLocalsHOLFinite mutated
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + added) nextEntries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed mutated finish cutoff nextCursor nextCursor next next accounts (TableFamily.PersistentFrame.of_memory cutoff nextCursor next mutated finish rfl) (Nat.le_refl _) rfl
  exact ⟨answerEq,empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,positive,funded,clock,forward,addedPositive,addedBound,capacityBound,finalFamily,finalImage,nextZone,price,
    codes,nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,nextSaved,finalRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan,markerPopulation,outerPopulation,accountPopulation,visits,populations⟩

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.balance_commit_return_normal
