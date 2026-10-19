import InitECandidate.Solver.Mpt.DestroyStorageAfterGet

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem whole_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address scratch transaction : BitVec 64)
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
    (innerReferences : ∀ item, property outer item → ∃ reader, (objects reader).pointer = item ∧ (objects reader).kind = .word)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64))
    (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added ≤ 1 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Get.bodyPrice (objects outer).kind (objects outer).slots.length + 1 + (if found then loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
          GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → next table = objects table) ∧
      ((found = false ∧ iterations = 0 ∧ added = 0 ∧ next = objects ∧ nextEntries = entries) ∨
        (found = true ∧ ∃ reader, (objects reader).kind = .word ∧ iterations = (objects reader).slots.length)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) := by
  obtain ⟨getPaid,flag,value,finish,getPositive,getBound,getFunded,binary,valueOwned,tailRun,postFrame⟩ := lookup_normal source post address transaction cursor objects outer
    family environment installed outerKind property values addressArena addressLocal transactionGlobal outerMapped outerStored returned normal
  let ready := lookupEntry source (objects outer).pointer getPaid flag value
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    simp [ready,lookupEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "m" ≠ ofString "addr" from by decide,show ofString "outer" ≠ ofString "addr" from by decide,addressLocal]
  have readyPair : ready.locals.lookup (ofString "m") = some (Get.pair flag value) := by
    simp [ready,lookupEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have readyOuter : ready.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)) := by
    simp [ready,lookupEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "m" ≠ ofString "outer" from by decide]
  obtain ⟨answerEq,found,iterations,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,price,codes,
    nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter⟩ := after_get_normal ready finish address scratch transaction flag value cursor cutoff objects writer outer base cap count entries
      readyFamily readyImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts readyRegistry property values owned savedValues writerKind outerKind addressArena scratchArena
      floors scratchBelow small journalAbove readyAddress readyPair binary valueOwned innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableBefore tableOutside
      readyOuter accountApart journal capacity counter returned tailRun
  have memory := congrArg PanSemStateFiniteExact.memory postFrame
  have domain := congrArg PanSemStateFiniteExact.memaddrs postFrame
  have endian := congrArg PanSemStateFiniteExact.be postFrame
  have globalEq := congrArg PanSemStateFiniteExact.globals postFrame
  have codeEq := congrArg PanSemStateFiniteExact.code postFrame
  have clockEq := congrArg PanSemStateFiniteExact.clock postFrame
  change post.memory = finish.memory at memory
  change post.memaddrs = finish.memaddrs at domain
  change post.be = finish.be at endian
  change post.globals = finish.globals at globalEq
  change post.code = finish.code at codeEq
  change post.clock = finish.clock at clockEq
  have finalFamily : TableFamily.Model post nextCursor next := models.of_control (by rw [globalEq]) memory domain endian
  have finalImage : Journal.Image post next base (count + added) nextEntries := nextImage.transfer domain (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => congrFun memory _) nextImage.separate
  have finalRegistry := nextRegistry.framed finish post cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next finish post memory) (Nat.le_refl _) domain
  have finalValues := nextValues.of_memory finish post next property memory.symm
  have startEffect := Journal.CounterEffect.unchanged source ready rfl
  have endEffect := Journal.CounterEffect.unchanged finish post (congrArg (fun map => map.lookup (ofString "journal_n")) globalEq)
  have finalEffect : Journal.CounterEffect source post added 0 0 := by
    simpa only [Nat.zero_add,Nat.add_zero] using (startEffect.trans effect).trans endEffect
  change paid ≤ source.clock - getPaid at funded
  change finish.clock = source.clock - getPaid - paid at clock
  refine ⟨answerEq,found,iterations,getPaid + paid,nextCursor,next,nextEntries,added,by omega,by omega,forward,addedBound,capacityBound,finalFamily,finalImage,nextZone,by omega,
    codeEq.trans codes,nextEnvironment.of_fields codeEq domain endian,?_,finalValues,nextSaved,finalRegistry,finalEffect,metadata,?_,others,branch,(by rw [globalEq]; exact nextCounter)⟩
  · intro key notHeap notCounter
    rw [globalEq]
    exact globals key notHeap notCounter
  · intro query above earlier outside away
    have step := frame query above earlier outside away
    exact ⟨step.1,(congrFun memory query).trans step.2⟩

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.whole_normal
