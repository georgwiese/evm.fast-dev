import InitECandidate.Solver.Mpt.TransientSetProgram
import InitECandidate.Solver.Mpt.DestroyStorageCode
import InitECandidate.Solver.MutableTable.GetNoException
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.TransientSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem delete_tail_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (query transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (queryArena : AllocatedBytes.Arena query 52)
    (queryLocal : source.locals.lookup (ofString "k") = some (.val (.word query)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 64#64)) (tableStored : source.memory (transaction + 64#64) = .word (objects writer).pointer)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (.seq deleteCall (.return (.const 0#64))) = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added ≤ 1 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Journal.Append.deletePrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ Journal.ProtectedFrame base cap cursor objects next source post ∧ TableFamily.Metadata objects next ∧
      (∀ reader,reader ≠ writer → next reader = objects reader) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧
      (∀ reader,(next reader).plan = (objects reader).plan) ∧ (∀ reader,(next reader).slots.length ≤ (objects reader).slots.length) := by
  have safe : Input.LocalPrefix (ofString "k") deleteCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨mutated,deleteRun,returnRun,keepQuery⟩ := safe.normal_continue source post (.return (.const 0#64)) returned normal
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [table,localVar "k"] =
      some [.val (.word (objects writer).pointer),.val (.word query)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,table,localVar,toExact,transactionGlobal,queryLocal,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,tableMapped,tableStored]
  have queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2^64 := by
    rw [writerKind]
    change query.toNat + 52 < 2^64
    have := queryArena.upper
    omega
  have queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind,
      source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)) := by
    rw [writerKind]
    intro offset inside
    exact AllocatedBytes.byte_mapped source query 52 offset environment.domain queryArena inside
  obtain ⟨paid,nextCursor,next,nextEntries,added,bounded,funded,clock,forward,addedBound,capacityBound,models,nextRegistry,nextImage,nextZone,nextValues,nextSaved,
    effect,frame,codes,nextEnvironment,globals,metadata,others,nextCounter,plans,populations⟩ := Journal.Append.delete_call_registered_values source mutated cursor objects writer base cap count entries
      family image zone countBound environment cutoff accounts registry accountApart query property values savedValues queryFits queryMapped
      (Get.original_code source.code installed) (DestroyStorage.table_delete_code source.code installed) (DestroyStorage.journal_delete_code source.code installed)
      journal capacity counter _ args deleteRun
  have returnedInfo := Input.return_normal mutated post (.const 0#64) returned returnRun
  have answerEq : returned = .val (.word 0#64) := Option.some.inj (returnedInfo.1.symm.trans rfl)
  rw [returnedInfo.2]
  let finish := emptyLocalsHOLFinite mutated
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + added) nextEntries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed mutated finish cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next mutated finish rfl) (Nat.le_refl _) rfl
  refine ⟨answerEq,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,finalFamily,finalImage,nextZone,?_,codes,
    nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,nextSaved,finalRegistry,effect,⟨frame.words⟩,metadata,others,nextCounter,plans,populations⟩
  rw [plans writer]
  omega

end InitECandidate.Solver.Mpt.TransientSet

#print axioms InitECandidate.Solver.Mpt.TransientSet.delete_tail_normal
