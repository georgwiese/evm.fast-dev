import InitECandidate.Solver.Mpt.DestroyStoragePresentLoop
import InitECandidate.Solver.MutableTable.GetNoException
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem present_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address scratch transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer reader outer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (readerKind : (objects reader).kind = .word) (outerKind : (objects outer).kind = .account)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (pairLocal : source.locals.lookup (ofString "m") = some (Get.pair 1#64 (objects reader).pointer))
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
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source present = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added ≤ 1 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        loopPrice (objects writer).slots.length (objects reader).slots.length + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 +
          GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → next table = objects table) := by
  classical
  obtain ⟨loopPaid,middleCursor,middleObjects,middle,finish,loopFunded,loopClock,loopForward,middleFamily,middleImage,middleZone,loopPriceBound,population,
    readerSame,codes,middleEnvironment,globals,middleValues,middleRegistry,loopFrame,metadata,others,middleOuter,middleAddress,tailRun,postFrame⟩ :=
    present_loop source post address scratch transaction cursor cutoff objects writer reader base cap count entries family image zone countBound environment installed
      accounts registry property values owned writerKind readerKind addressArena scratchArena floors scratchBelow small journalAbove addressLocal pairLocal
      scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableBefore tableOutside returned normal
  have safe : Input.LocalPrefix (ofString "addr") removeCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨deleted,deleteRun,returnRun,keepAddress⟩ := safe.normal_continue middle finish (.return (.const 0#64)) returned tailRun
  have returnInfo := Input.return_normal deleted finish (.const 0#64) returned returnRun
  have answerEq : returned = .val (.word 0#64) := Option.some.inj (returnInfo.1.symm.trans rfl)
  have completeFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite deleted := by
    rw [postFrame,returnInfo.2]
    rfl
  have middleInstalled : Input.OriginalCode.Installed middle.code := by rw [codes]; exact installed
  have outerWord : middle.locals.lookup (ofString "outer") = some (.val (.word (middleObjects outer).pointer)) := by
    rw [metadata.pointers outer]
    exact middleOuter.trans outerLocal
  have args : evalListHOLFinite middle (h := fun query => Classical.propDecidable (middle.memaddrs query)) [localVar "outer",localVar "addr"] =
      some [.val (.word (middleObjects outer).pointer),.val (.word address)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,outerWord,middleAddress]
  have queryFits : address.toNat + KeyHash.keySize (middleObjects outer).kind < 2^64 := by
    rw [metadata.kinds outer,outerKind]
    change address.toNat + 20 < 2^64
    have := addressArena.upper
    omega
  have queryMapped : ∀ offset < KeyHash.keySize (middleObjects outer).kind,
      middle.memaddrs (panByteAlignHOL (width := 64) (byteAddress address offset)) := by
    rw [metadata.kinds outer,outerKind]
    intro offset inside
    exact AllocatedBytes.byte_mapped middle address 20 offset middleEnvironment.domain addressArena inside
  obtain ⟨deletePaid,nextCursor,next,nextEntries,added,deletePriceBound,deleteFunded,deleteClock,deleteForward,addedBound,capacityBound,models,
    nextRegistry,nextImage,nextZone,nextValues,nextSaved,deleteEffect,deleteFrame,deleteCodes,nextEnvironment,deleteGlobals,deleteMetadata,deleteOthers⟩ :=
    Journal.Append.delete_call_registered_values middle deleted middleCursor middleObjects outer base cap count entries middleFamily middleImage middleZone countBound
      middleEnvironment cutoff accounts middleRegistry accountApart address property middleValues savedValues queryFits queryMapped
      (Get.original_code middle.code middleInstalled) (table_delete_code middle.code middleInstalled) (journal_delete_code middle.code middleInstalled)
      ((globals (ofString "journal") (by decide)).trans journal) ((globals (ofString "journal_cap") (by decide)).trans capacity)
      ((globals (ofString "journal_n") (by decide)).trans counter) _ args deleteRun
  have memory := congrArg PanSemStateFiniteExact.memory completeFrame
  have domain := congrArg PanSemStateFiniteExact.memaddrs completeFrame
  have endian := congrArg PanSemStateFiniteExact.be completeFrame
  have globalEq := congrArg PanSemStateFiniteExact.globals completeFrame
  have codeEq := congrArg PanSemStateFiniteExact.code completeFrame
  have clock := congrArg PanSemStateFiniteExact.clock completeFrame
  change post.memory = deleted.memory at memory
  change post.memaddrs = deleted.memaddrs at domain
  change post.be = deleted.be at endian
  change post.globals = deleted.globals at globalEq
  change post.code = deleted.code at codeEq
  change post.clock = deleted.clock at clock
  have finalFamily : TableFamily.Model post nextCursor next := models.of_control (by rw [globalEq]) memory domain endian
  have finalImage : Journal.Image post next base (count + added) nextEntries :=
    nextImage.transfer domain (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => congrFun memory _) nextImage.separate
  have finalRegistry := nextRegistry.framed deleted post cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next deleted post memory) (Nat.le_refl _) domain
  have finalValues := nextValues.of_memory deleted post next property memory.symm
  have initialEffect := Journal.CounterEffect.unchanged source middle (globals (ofString "journal_n") (by decide))
  have finalEffect := Journal.CounterEffect.unchanged deleted post (congrArg (fun map => map.lookup (ofString "journal_n")) globalEq)
  have effect : Journal.CounterEffect source post added 0 0 := by
    simpa only [Nat.zero_add,Nat.add_zero] using (initialEffect.trans deleteEffect).trans finalEffect
  have different : outer ≠ writer := by
    intro same
    rw [same,writerKind] at outerKind
    cases outerKind
  have outerSame := others outer different
  have writerSame := deleteOthers writer (Ne.symm different)
  rw [outerSame] at deletePriceBound
  have price : loopPaid + deletePaid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
      loopPrice (objects writer).slots.length (objects reader).slots.length + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 +
        GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity := by
    rw [writerSame]
    omega
  refine ⟨answerEq,loopPaid + deletePaid,nextCursor,next,nextEntries,added,by omega,by omega,by omega,addedBound,capacityBound,finalFamily,finalImage,nextZone,price,
    codeEq.trans (deleteCodes.trans codes),nextEnvironment.of_fields codeEq domain endian,?_,finalValues,nextSaved,finalRegistry,effect,metadata.trans deleteMetadata,?_,?_⟩
  · intro key notHeap notCounter
    rw [globalEq]
    exact (deleteGlobals key notHeap notCounter).trans (globals key notHeap)
  · intro query above earlier outside away
    have first := loopFrame.words query above earlier outside
    have second := deleteFrame.words query (by omega) first.1 away
    exact ⟨second.1,(congrFun memory query).trans (second.2.trans first.2)⟩
  · intro table notWriter notOuter
    exact (deleteOthers table notOuter).trans (others table notWriter)

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.present_normal
