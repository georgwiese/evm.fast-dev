import InitECandidate.Solver.Mpt.AccountBalanceSetAfterCopy
import InitECandidate.Solver.Mpt.AccountCopyAssigned
import InitECandidate.Solver.Mpt.AccountValueExtension
import InitECandidate.Solver.GasBudget.JournalPersistentFrame

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_get_normal {ι : Type} [DecidableEq ι]
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
    (accountMember : account ∈ accounts)
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
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64))
    (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (outerBefore : (transaction + 32#64).toNat < cursor)
    (outerOutside : TableFamily.Outside objects (transaction + 32#64)) (outerAway : Journal.Away base cap (transaction + 32#64))
    (accountMapped : source.memaddrs (transaction + 16#64))
    (accountStored : source.memory (transaction + 16#64) = .word (objects accountWriter).pointer)
    (accountAbove : cutoff ≤ (transaction + 16#64).toNat) (accountBefore : (transaction + 16#64).toNat < cursor)
    (accountOutside : TableFamily.Outside objects (transaction + 16#64)) (accountAway : Journal.Away base cap (transaction + 16#64))
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterGet = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧
    ∃ (empty : BitVec 64) (destroyed found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      1 ≤ paid ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ 1 ≤ added ∧ added ≤ 3 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (objects accountWriter).plan.capacity ≤
        Journal.Append.setPrice (objects accountWriter).kind (objects accountWriter).slots.length + 17 + (if destroyed then Get.bodyPrice (objects outer).kind (objects outer).slots.length + 3 +
          (if found then DestroyStorage.loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
          Journal.Append.setPrice (objects accountWriter).kind ((objects accountWriter).slots.length + 1) + 2 else 0) +
          GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (next accountWriter).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next (AccountValueExtension.added property accountWriter (BitVec.ofNat 64 cursor)) ∧
      Journal.EntryValues nextEntries (count + added) (AccountValueExtension.added property accountWriter (BitVec.ofNat 64 cursor)) ∧ AccountDecode.Registry post cutoff nextCursor next (accounts ++ [BitVec.ofNat 64 cursor]) ∧
      AccountDecode.Registry.Extension accounts (accounts ++ [BitVec.ofNat 64 cursor]) cursor ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → table ≠ accountWriter → next table = objects table) ∧
      ((found = false ∧ iterations = 0) ∨
        (found = true ∧ ∃ reader, (objects reader).kind = .word ∧ iterations = (objects reader).slots.length)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧ destroyed = decide (empty ≠ 0#64) ∧ (empty = 0#64 ∨ empty = 1#64) ∧ (if destroyed then 2 ≤ added else added = 1 ∧ found = false ∧ iterations = 0) ∧ (next outer).plan = (objects outer).plan := by
  let heap := BitVec.ofNat 64 cursor
  have table := family.tables writer
  have heapNumber : heap.toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := table.bounded; omega)]
  have currentFamily : TableFamily.Model source heap.toNat objects := by rw [heapNumber]; exact family
  have currentRegistry : AccountDecode.Registry source cutoff heap.toNat objects accounts := by rw [heapNumber]; exact registry
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "a"] = some [.val (.word account)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,accountLocal]
  have safe : Input.LocalPrefix (ofString "addr") copyCall := .call (some (ofString "a")) _ _ (by
    intro name same
    have nameEq : name = ofString "a" := Option.some.inj same.symm
    rw [nameEq]
    decide)
  obtain ⟨copied,copyRun,tailRun,keepAddress⟩ := safe.normal_continue source post afterCopy returned normal
  obtain ⟨copyFunded,room,copyClock,copyLocals,copyCode,copyDomain,copyEndian,copyGlobals,copyImage,copyWindow,copyHeap,copyFamily,copyRegistry,copyValues,extension,copyFrame⟩ :=
    AccountCopy.assigned_registered source copied account heap cutoff objects accounts currentFamily currentRegistry property values accountMember table.heap (by rw [heapNumber]; exact table.bounded)
      (by rw [heapNumber]; exact table.aligned) installed "a" [localVar "a"] accountLocal args copyRun
  rw [heapNumber] at room copyHeap copyFamily copyRegistry extension copyFrame
  let nextProperty := AccountValueExtension.added property accountWriter heap
  have nextValues := AccountValueExtension.live_values copied objects property copyValues accountWriter heap
  have nextSaved := AccountValueExtension.saved_values entries count property savedValues accountWriter heap
  obtain ⟨copyJournal,copyZone⟩ := Journal.image_zone_framed source copied cursor (cursor + 56) cutoff base cap count objects objects entries image zone countBound (by omega) journalAbove copyFrame (TableFamily.Metadata.refl objects) copyDomain
  have copyEnvironment := environment.of_fields copyCode copyDomain copyEndian
  have copyInstalled : Input.OriginalCode.Installed copied.code := by rw [copyCode]; exact installed
  have copyAddress : copied.locals.lookup (ofString "addr") = some (.val (.word address)) := keepAddress.trans addressLocal
  have copyAccount : copied.locals.lookup (ofString "a") = some (.val (.word heap)) := by rw [copyLocals]; simp [HolFiniteMapExact.update,FUPDATE]
  have copyAmount : copied.locals.lookup (ofString "amount") = some (Input.RlpWrite.U256Value.tuple words) := by
    rw [copyLocals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "a" ≠ ofString "amount" by decide] using amountLocal
  have copyReferences : ∀ item,nextProperty outer item → ∃ reader,(objects reader).pointer = item ∧ (objects reader).kind = .word := by
    intro item ownedItem
    exact innerReferences item ((AccountValueExtension.other property accountWriter outer heap item (Ne.symm differentOuter)).mp ownedItem)
  have copyApart := extension.journal_apart accountApart zone.earlier
  have copyWord (query : BitVec 64) (before : query.toNat < cursor) : copied.memory query = source.memory query := copyWindow query (Or.inl (by rw [heapNumber]; exact before))
  have mapped (query : BitVec 64) (mapping : source.memaddrs query) : copied.memaddrs query := by rw [copyDomain]; exact mapping
  obtain ⟨answerEq,empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,positive,funded,clock,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,price,codes,nextEnvironment,globals,
    finalValues,finalSaved,finalRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan⟩ := after_copy_normal copied post address heap emptyHash scratch transaction (cursor + 56) cutoff cursor objects writer outer accountWriter
      base cap count entries copyFamily copyJournal copyZone countBound copyEnvironment copyInstalled (accounts ++ [heap]) copyRegistry nextProperty nextValues (Or.inl owned) (Or.inl accountOwned) (Or.inr ⟨rfl,rfl⟩) nextSaved
      writerKind outerKind accountKind differentOuter addressArena scratchArena floors scratchBelow small journalAbove (by simp) (by rw [heapNumber]) words copyAddress copyAccount copyAmount
      ((copyGlobals (ofString "empty_code_hash") (by decide)).trans emptyGlobal) emptyArena copyReferences ((copyGlobals (ofString "sk_buf") (by decide)).trans scratchGlobal)
      ((copyGlobals (ofString "ts") (by decide)).trans transactionGlobal)
      (mapped _ tableMapped) ((copyWord _ tableBefore).trans tableStored) tableAbove tableAway tableBefore tableOutside
      (mapped _ outerMapped) ((copyWord _ outerBefore).trans outerStored) outerBefore outerOutside outerAway
      (mapped _ accountMapped) ((copyWord _ accountBefore).trans accountStored) accountAbove accountBefore accountOutside accountAway copyApart
      ((copyGlobals (ofString "journal") (by decide)).trans journal) ((copyGlobals (ofString "journal_cap") (by decide)).trans capacity) ((copyGlobals (ofString "journal_n") (by decide)).trans counter) returned tailRun
  rw [copyClock] at funded clock
  have totalFunded : 7 + paid ≤ source.clock := by
    calc
      _ ≤ 7 + (source.clock - 7) := Nat.add_le_add_left funded _
      _ = source.clock := Nat.add_sub_of_le copyFunded
  have totalClock : post.clock = source.clock - (7 + paid) := by rw [clock,Nat.sub_sub]
  have totalGlobals : Journal.OtherGlobals source post := by intro name notHeap notCounter; exact (globals name notHeap notCounter).trans (copyGlobals name notHeap)
  have copyEffect := Journal.CounterEffect.unchanged source copied (copyGlobals (ofString "journal_n") (by decide))
  have totalEffect : Journal.CounterEffect source post added 0 0 := by simpa only [Nat.zero_add,Nat.add_zero] using copyEffect.trans effect
  refine ⟨answerEq,empty,destroyed,found,iterations,7 + paid,nextCursor,next,nextEntries,added,by omega,totalFunded,totalClock,by omega,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,by omega,
    codes.trans copyCode,nextEnvironment,totalGlobals,finalValues,finalSaved,finalRegistry,extension,totalEffect,metadata,?_,others,branch,nextCounter,decision,binary,appends,outerPlan⟩
  intro query above before outside away
  obtain ⟨nextOutside,same⟩ := frame query above before outside away
  exact ⟨nextOutside,same.trans (copyWord query before)⟩

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.after_get_normal
