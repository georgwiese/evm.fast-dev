import InitECandidate.Solver.Mpt.AccountEtherCreateProgram
import InitECandidate.Solver.GasBudget.U256ArithmeticCall
import InitECandidate.Solver.Mpt.AccountIsEmptyReads

namespace InitECandidate.Solver.Mpt.AccountEtherCreate
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
        Journal.Append.setPrice (objects accountWriter).kind (objects accountWriter).slots.length + 11 + (if destroyed then Get.bodyPrice (objects outer).kind (objects outer).slots.length + 3 +
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
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧ destroyed = decide (empty ≠ 0#64) ∧ (empty = 0#64 ∨ empty = 1#64) ∧ (if destroyed then 2 ≤ added else added = 1 ∧ found = false ∧ iterations = 0) ∧ (next outer).plan = (objects outer).plan ∧
      (next writer).slots.length ≤ (objects writer).slots.length + iterations ∧ (next outer).slots.length ≤ (objects outer).slots.length ∧ (next accountWriter).slots.length ≤ (objects accountWriter).slots.length + 2 := by
  classical
  obtain ⟨accountImage⟩ := registry.images account accountMember
  let oldWords := Input.RlpWrite.U256Value.memoryWords source (account + 8#64)
  let newWords := U256Add.result oldWords words
  have loadRead : evalHOLExact (toExact source) (.load Input.RlpWrite.U256Value.tupleShape (.op .add [localVar "a",.const 8#64])) = some (Input.RlpWrite.U256Value.tuple oldWords) := by
    simpa [eval,AccountIsEmpty.field,oldWords] using AccountIsEmpty.balance_read source account accountImage accountLocal
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) addArguments =
      some [Input.RlpWrite.U256Value.tuple oldWords,Input.RlpWrite.U256Value.tuple words] := by
    rw [evalListHOLFinite,addArguments,evalListHOLExact,loadRead]
    simp [evalListHOLExact,evalHOLExact,localVar,toExact,amountLocal]
  obtain ⟨positive,inner,tailRun,scope⟩ := U256Add.success_prefix source post oldWords words "nb" addArguments (AccountBalanceSet.afterBalance (localVar "nb")) args
    (U256Add.original_code source.code installed) returned normal
  let ready := setVarHOLFinite (ofString "nb") (Input.RlpWrite.U256Value.tuple newWords) {source with clock := source.clock - 1}
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "nb" ≠ ofString "addr" by decide] using addressLocal
  have readyAccount : ready.locals.lookup (ofString "a") = some (.val (.word account)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "nb" ≠ ofString "a" by decide] using accountLocal
  have readValue : eval ready (localVar "nb") = some (Input.RlpWrite.U256Value.tuple newWords) := by
    simp [eval,evalHOLExact,localVar,toExact,ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨answerEq,empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,paymentPositive,funded,clock,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,price,codes,nextEnvironment,globals,
    nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan,markerPopulation,outerPopulation,accountPopulation⟩ := AccountBalanceSet.after_balance_normal ready inner address account emptyHash scratch transaction cursor cutoff protectedCursor objects writer outer accountWriter
      base cap count entries readyFamily readyImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts readyRegistry property values owned accountOwned publishOwned savedValues writerKind outerKind accountKind differentOuter
      addressArena scratchArena floors scratchBelow small journalAbove accountMember protectedBefore newWords (localVar "nb") readyAddress readyAccount readValue emptyGlobal emptyArena innerReferences scratchGlobal transactionGlobal
      tableMapped tableStored tableAbove tableAway tableBefore tableOutside outerMapped outerStored outerBefore outerOutside outerAway accountMapped accountStored accountAbove accountBefore accountOutside accountAway accountApart journal capacity counter returned tailRun
  rw [scope]
  let finish := restore source "nb" inner
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + added) nextEntries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed inner finish cutoff nextCursor nextCursor next next accounts (TableFamily.PersistentFrame.of_memory cutoff nextCursor next inner finish rfl) (Nat.le_refl _) rfl
  change paid ≤ source.clock - 1 at funded
  change inner.clock = source.clock - 1 - paid at clock
  exact ⟨answerEq,empty,destroyed,found,iterations,1 + paid,nextCursor,next,nextEntries,added,by omega,by omega,by change inner.clock = _; omega,forward,addedPositive,addedBound,capacityBound,finalFamily,finalImage,nextZone,by omega,
    codes,nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,nextSaved,finalRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan,markerPopulation,outerPopulation,accountPopulation⟩

end InitECandidate.Solver.Mpt.AccountEtherCreate

#print axioms InitECandidate.Solver.Mpt.AccountEtherCreate.after_copy_normal
