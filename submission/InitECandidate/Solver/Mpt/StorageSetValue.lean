import InitECandidate.Solver.Mpt.StorageSetProgram
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.Mpt.Value32Allocation
import InitECandidate.Solver.Mpt.AccountSetProgram
import InitECandidate.Solver.GasBudget.JournalAppendSetRegistered

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem allocate_tail_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (query : BitVec 64) (words : Input.RlpWrite.U256Value.Words)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (freshOwned : ∀ pointer,AllocatedBytes.Arena pointer 32 → pointer.toNat % 8 = 0 → property writer pointer)
    (writerKind : (objects writer).kind = .word) (queryArena : AllocatedBytes.Arena query 32)
    (queryLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (tableLocal : source.locals.lookup (ofString "inner") = some (.val (.word (objects writer).pointer)))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source allocate = (some (.returned returned),post)) :
    count < cap ∧ returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (oldFlag oldValue : BitVec 64),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor + 32 ≤ nextCursor ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Journal.Image post (Function.update objects writer next) base (count + 1)
        (Function.update entries count ⟨writer,BitVec.ofNat 64 (cursor + 32),oldFlag,oldValue⟩) ∧ Journal.Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Journal.Append.setPrice (objects writer).kind (objects writer).slots.length + 2 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧ post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧
      Journal.EntryValues (Function.update entries count ⟨writer,BitVec.ofNat 64 (cursor + 32),oldFlag,oldValue⟩) (count + 1) property ∧
      AccountDecode.Registry post cutoff nextCursor (Function.update objects writer next) accounts ∧ Journal.CounterEffect source post 1 0 0 ∧
      Journal.ProtectedFrame base cap cursor objects (Function.update objects writer next) source post ∧ TableFamily.Metadata objects (Function.update objects writer next) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) := by
  obtain ⟨room,allocPositive,valueArena,valueAligned,readyFamily,readyImage,readyZone,readyRegistry,readyValues,valueFrame,valueGlobals,finish,tailRun,scope⟩ :=
    Value32.prefix_normal source post cursor cutoff objects writer accounts family registry property values base cap count entries image zone countBound environment words valueLocal
      (.seq setCall (.return (.const 0#64))) returned normal
  let ready := Value32.stored source cursor words
  have safe : Input.LocalPrefix (ofString "key") setCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨mutated,setRun,returnRun,keepQuery⟩ := safe.normal_continue ready finish (.return (.const 0#64)) returned tailRun
  have readyQuery : ready.locals.lookup (ofString "key") = some (.val (.word query)) := by
    simpa [ready,Value32.stored,Value32.allocated,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "v" ≠ ofString "key" from by decide] using queryLocal
  have valuePointer : ready.locals.lookup (ofString "v") = some (.val (.word (BitVec.ofNat 64 cursor))) := bind_lookup_same _ _ _
  have readyTable : ready.locals.lookup (ofString "inner") = some (.val (.word (objects writer).pointer)) := by
    simpa [ready,Value32.stored,Value32.allocated,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "v" ≠ ofString "inner" from by decide] using tableLocal
  have args : evalListHOLFinite ready (h := fun address => Classical.propDecidable (ready.memaddrs address)) [localVar "inner",localVar "key",localVar "v"] =
      some (TableCall.values (objects writer).pointer query (BitVec.ofNat 64 cursor)) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,readyTable,readyQuery,valuePointer,TableCall.values]
  have readyEnvironment : WarmKeys.Environment ready := environment.of_fields rfl rfl rfl
  have queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2^64 := by
    rw [writerKind]
    change query.toNat + 32 < 2^64
    have := queryArena.upper
    omega
  have queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind,
      ready.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)) := by
    rw [writerKind]
    intro offset inside
    exact AllocatedBytes.byte_mapped ready query 32 offset environment.domain queryArena inside
  obtain ⟨countRoom,setPaid,nextCursor,next,oldFlag,oldValue,setPositive,setFunded,setClock,forward,nextKind,binary,models,nextImage,nextZone,price,population,nextCounter,
    locals,codes,nextEnvironment,globals,effect,setFrame,nextValues,nextSaved,nextRegistry,metadata⟩ := Journal.Append.set_call_registered_values ready mutated (cursor + 32) objects writer base cap count entries
      readyFamily readyImage readyZone countBound readyEnvironment cutoff accounts readyRegistry accountApart query (BitVec.ofNat 64 cursor) property readyValues (freshOwned _ valueArena valueAligned) savedValues
      queryFits queryMapped (Get.original_code source.code installed) (AccountSet.journal_code source.code installed)
      ((valueGlobals (ofString "journal") (by decide)).trans journal) ((valueGlobals (ofString "journal_cap") (by decide)).trans capacity)
      ((valueGlobals (ofString "journal_n") (by decide)).trans counter) _ args setRun
  have returnedInfo := Input.return_normal mutated finish (.const 0#64) returned returnRun
  have answerEq : returned = .val (.word 0#64) := Option.some.inj (returnedInfo.1.symm.trans rfl)
  rw [scope,returnedInfo.2]
  let target := restore source "v" (emptyLocalsHOLFinite mutated)
  have finalFamily : TableFamily.Model target nextCursor (Function.update objects writer next) := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image target (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer,BitVec.ofNat 64 (cursor + 32),oldFlag,oldValue⟩) :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed mutated target cutoff nextCursor nextCursor (Function.update objects writer next) (Function.update objects writer next) accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor _ mutated target rfl) (Nat.le_refl _) rfl
  have initialEffect := Journal.CounterEffect.unchanged source ready ((valueGlobals (ofString "journal_n") (by decide)))
  have finalEffect : Journal.CounterEffect source target 1 0 0 := by
    change Journal.CounterEffect source mutated 1 0 0
    simpa only [Nat.zero_add,Nat.add_zero] using initialEffect.trans effect
  have finalGlobals : Journal.OtherGlobals source target := by
    intro key notHeap notCounter
    exact (globals key notHeap notCounter).trans (valueGlobals key notHeap)
  change setPaid ≤ source.clock - 1 at setFunded
  change mutated.clock = source.clock - 1 - setPaid at setClock
  refine ⟨countRoom,answerEq,1 + setPaid,nextCursor,next,oldFlag,oldValue,by omega,by change mutated.clock = _; omega,forward,finalFamily,finalImage,nextZone,by omega,population,codes,
    nextEnvironment.of_fields rfl rfl rfl,finalGlobals,nextValues,nextSaved,finalRegistry,finalEffect,⟨?_⟩,metadata,nextCounter⟩
  intro address earlier outside away
  have step := setFrame.words address (by omega) outside away
  exact ⟨step.1,step.2.trans (Value32.writes_earlier source.memory cursor words room address earlier)⟩

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.allocate_tail_normal
