import InitECandidate.Solver.Mpt.AccountBalanceSetProgram
import InitECandidate.Solver.Mpt.AccountCommitCall
import InitECandidate.Solver.Mpt.AccountMutationWrites
import InitECandidate.Solver.Mpt.AccountStoreRegistered

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_copy_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address account emptyHash scratch transaction : BitVec 64)
    (cursor cutoff protectedCursor : Nat) (objects : ι → TableFamily.Object) (writer outer accountWriter : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
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
    (words : Input.RlpWrite.U256Value.Words)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (accountLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
    (amountLocal : source.locals.lookup (ofString "amount") = some (Input.RlpWrite.U256Value.tuple words))
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
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCopy = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧
    ∃ (empty : BitVec 64) (destroyed found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      1 ≤ paid ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ 1 ≤ added ∧ added ≤ 3 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (objects accountWriter).plan.capacity ≤
        Journal.Append.setPrice (objects accountWriter).kind (objects accountWriter).slots.length + 10 + (if destroyed then Get.bodyPrice (objects outer).kind (objects outer).slots.length + 3 +
          (if found then DestroyStorage.loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
          Journal.Append.setPrice (objects accountWriter).kind ((objects accountWriter).slots.length + 1) + 2 else 0) +
          GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (next accountWriter).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < protectedCursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → table ≠ accountWriter → next table = objects table) ∧
      ((found = false ∧ iterations = 0) ∨
        (found = true ∧ ∃ reader, (objects reader).kind = .word ∧ iterations = (objects reader).slots.length)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧ destroyed = decide (empty ≠ 0#64) ∧ (empty = 0#64 ∨ empty = 1#64) ∧ (if destroyed then 2 ≤ added else added = 1 ∧ found = false ∧ iterations = 0) ∧ (next outer).plan = (objects outer).plan := by
  obtain ⟨accountImage⟩ := registry.images account accountMember
  have objectBefore := registry.before account accountMember
  have destinationRead : eval source (.op .add [localVar "a",.const 8#64]) = some (.val (.word (account + 8#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,accountLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  have valueRead : eval source (localVar "amount") = some (Input.RlpWrite.U256Value.tuple words) := by
    simp [eval,evalHOLExact,localVar,toExact,amountLocal]
  obtain ⟨storeActual,writtenFamily,writtenRegistry,writtenValues⟩ := registry.balance_store source cutoff cursor objects accounts family property values account accountMember _ _ words destinationRead valueRead
  let writes := Input.RlpWrite.U256Value.wordWrites (account + 8#64) words
  let written := {source with memory := WordWrites.write source.memory writes}
  have contained : ∀ entry ∈ writes,∃ offset : Nat,offset < 56 ∧ entry.1 = account + BitVec.ofNat 64 offset := by
    intro entry member
    simp only [writes,Input.RlpWrite.U256Value.wordWrites,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨8,by decide,rfl⟩
    · exact ⟨16,by decide,by simp [BitVec.add_assoc]⟩
    · exact ⟨24,by decide,by simp [BitVec.add_assoc]⟩
    · exact ⟨32,by decide,by simp [BitVec.add_assoc]⟩
  have window := AccountDecode.object_writes_window source account accountImage writes contained
  have writtenImage := AccountDecode.journal_after_object_writes source objects base cap count cursor entries image zone countBound account accountImage (accountApart account accountMember) writes contained
  have storeRun : evaluateHOLFiniteState source balanceStore = (none,written) := storeActual
  have tailRun : evaluateHOLFiniteState written (.seq commitCall (.return (.const 0#64))) = (some (.returned returned),post) := by
    have execute := StateSteps.next_sequence source written balanceStore (.seq commitCall (.return (.const 0#64))) storeRun (Nat.le_refl _)
    exact execute.symm.trans normal
  have safe : Input.LocalPrefix (ofString "addr") commitCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨mutated,commitRun,returnRun,keepAddress⟩ := safe.normal_continue written post (.return (.const 0#64)) returned tailRun
  have args : evalListHOLFinite written (h := fun query => Classical.propDecidable (written.memaddrs query)) [localVar "addr",localVar "a"] = some (AccountSet.values address account) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,show written.locals = source.locals from rfl,addressLocal,accountLocal,AccountSet.values]
  have earlier (query : BitVec 64) (before : query.toNat < protectedCursor) : written.memory query = source.memory query := window query (Or.inl (by omega))
  have writtenTable : written.memory (transaction + 24#64) = .word (objects writer).pointer := (earlier _ tableBefore).trans tableStored
  have writtenOuter : written.memory (transaction + 32#64) = .word (objects outer).pointer := (earlier _ outerBefore).trans outerStored
  have writtenAccount : written.memory (transaction + 16#64) = .word (objects accountWriter).pointer := (earlier _ accountBefore).trans accountStored
  obtain ⟨empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,positive,funded,clock,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,price,locals,codes,nextEnvironment,globals,
    nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan⟩ := AccountCommit.call_normal written mutated address account emptyHash scratch transaction cursor cutoff objects writer outer accountWriter base cap count entries
      writtenFamily writtenImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts writtenRegistry property writtenValues owned accountOwned publishOwned savedValues writerKind outerKind accountKind differentOuter
      addressArena scratchArena floors scratchBelow small journalAbove accountMember emptyGlobal emptyArena innerReferences scratchGlobal transactionGlobal tableMapped writtenTable tableAbove tableAway (by omega) tableOutside
      outerMapped writtenOuter (by omega) outerOutside outerAway accountMapped writtenAccount accountAbove (by omega) accountOutside accountAway accountApart journal capacity counter _ args commitRun
  have returnedInfo := Input.return_normal mutated post (.const 0#64) returned returnRun
  have answerEq : returned = .val (.word 0#64) := Option.some.inj (returnedInfo.1.symm.trans rfl)
  rw [returnedInfo.2]
  let finish := emptyLocalsHOLFinite mutated
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + added) nextEntries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed mutated finish cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next mutated finish rfl) (Nat.le_refl _) rfl
  refine ⟨answerEq,empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,positive,funded,clock,forward,addedPositive,addedBound,capacityBound,finalFamily,finalImage,nextZone,price,
    codes,nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,nextSaved,finalRegistry,effect,metadata,?_,others,branch,nextCounter,decision,binary,appends,outerPlan⟩
  intro query above before outside away
  obtain ⟨nextOutside,same⟩ := frame query above (by omega) outside away
  exact ⟨nextOutside,same.trans (earlier query before)⟩

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.after_copy_normal
