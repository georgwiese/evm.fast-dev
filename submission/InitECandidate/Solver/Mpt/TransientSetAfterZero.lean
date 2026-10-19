import InitECandidate.Solver.Mpt.TransientSetNonzero

namespace InitECandidate.Solver.Mpt.TransientSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_zero_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (query transaction zero : BitVec 64) (words : Input.RlpWrite.U256Value.Words)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (freshOwned : ∀ pointer,AllocatedBytes.Arena pointer 32 → pointer.toNat % 8 = 0 → property writer pointer)
    (writerKind : (objects writer).kind = .storage) (queryArena : AllocatedBytes.Arena query 52)
    (queryLocal : source.locals.lookup (ofString "k") = some (.val (.word query)))
    (zeroLocal : source.locals.lookup (ofString "z") = some (.val (.word zero)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 64#64)) (tableStored : source.memory (transaction + 64#64) = .word (objects writer).pointer)
    (tableBefore : (transaction + 64#64).toNat < cursor)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterZero = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (removed : Bool) (paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added ≤ 1 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        (if removed then Journal.Append.deletePrice (objects writer).kind (objects writer).slots.length + 1 else Journal.Append.setPrice (objects writer).kind (objects writer).slots.length + 2) + GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ Journal.ProtectedFrame base cap cursor objects next source post ∧ TableFamily.Metadata objects next ∧
      (∀ reader,reader ≠ writer → next reader = objects reader) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧
      (next writer).slots.length ≤ (objects writer).slots.length + 1 ∧ removed = decide (zero ≠ 0#64) ∧ (removed = false → added = 1) := by
  have dispatch := zero_dispatch source zero zeroLocal
  by_cases absent : zero = 0#64
  · rw [if_pos absent] at dispatch
    rw [dispatch] at normal
    obtain ⟨room,answerEq,paid,nextCursor,next,flag,oldValue,funded,clock,forward,models,nextImage,nextZone,price,population,codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,frame,metadata,nextCounter⟩ :=
      allocate_tail_normal source post query transaction words cursor cutoff objects writer base cap count entries family image zone countBound environment installed accounts registry accountApart
        property values savedValues freshOwned writerKind queryArena queryLocal valueLocal transactionGlobal tableMapped tableStored tableBefore journal capacity counter returned normal
    let nextObjects := Function.update objects writer next
    let nextEntries := Function.update entries count ⟨writer,BitVec.ofNat 64 (cursor + 32),flag,oldValue⟩
    exact ⟨answerEq,false,paid,nextCursor,nextObjects,nextEntries,1,funded,clock,by omega,by decide,by omega,models,nextImage,nextZone,by simpa [nextObjects] using price,
      codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,frame,metadata,(fun reader other => Function.update_of_ne other next objects),nextCounter,
      by simpa [nextObjects] using population,by simp [absent],by intro same; rfl⟩
  · rw [if_neg absent] at dispatch
    rw [dispatch] at normal
    obtain ⟨answerEq,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,price,codes,nextEnvironment,globals,nextValues,
      nextSaved,nextRegistry,effect,frame,metadata,others,nextCounter,plans,populations⟩ := delete_tail_normal source post query transaction cursor cutoff objects writer base cap count entries
        family image zone countBound environment installed accounts registry accountApart property values savedValues writerKind queryArena queryLocal transactionGlobal tableMapped tableStored
        journal capacity counter returned normal
    exact ⟨answerEq,true,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,by simpa using price,
      codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,frame,metadata,others,nextCounter,by have bound := populations writer; omega,
      by simp [absent],by intro impossible; cases impossible⟩

end InitECandidate.Solver.Mpt.TransientSet

#print axioms InitECandidate.Solver.Mpt.TransientSet.after_zero_normal
