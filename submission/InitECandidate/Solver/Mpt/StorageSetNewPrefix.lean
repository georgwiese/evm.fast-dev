import InitECandidate.Solver.Mpt.StorageSetNewProgram
import InitECandidate.Solver.Mpt.AccountSetProgram
import InitECandidate.Solver.GasBudget.JournalAppendSetRegistered
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem new_prefix_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (outer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (outerKind : (objects outer).kind = .account) (addressArena : AllocatedBytes.Arena address 20)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (outerLocal : source.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)))
    (innerLocal : source.locals.lookup (ofString "inner") = some (.val (.word 0#64)))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source newBranch = (some (.returned returned),post)) :
    count < cap ∧ ∃ (paid nextCursor : Nat) (published : TableFamily.Object) (oldFlag oldValue : BitVec 64) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧ freshEnd .word cursor 8 ≤ nextCursor ∧
      TableFamily.Model ready nextCursor (Function.update (TableFamily.extend objects (Journal.newObject .word cursor 8)) (some outer) published) ∧
      Journal.Image ready (Function.update (TableFamily.extend objects (Journal.newObject .word cursor 8)) (some outer) published) base (count + 1)
        (Function.update (fun index => (entries index).lift) count ⟨some outer,BitVec.ofNat 64 (freshEnd .word cursor 8),oldFlag,oldValue⟩) ∧
      Journal.Zone (Function.update (TableFamily.extend objects (Journal.newObject .word cursor 8)) (some outer) published) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects outer).kind (objects outer).plan.capacity ≤
        TableRuntime.price 8 + 1 + Journal.Append.setPrice (objects outer).kind (objects outer).slots.length + 1 + GrowRuntime.growthPotential (objects outer).kind published.plan.capacity ∧
      published.slots.length ≤ (objects outer).slots.length + 1 ∧ ready.code = source.code ∧ WarmKeys.Environment ready ∧ Journal.OtherGlobals source ready ∧
      TableFamily.ValuesHave ready (Function.update (TableFamily.extend objects (Journal.newObject .word cursor 8)) (some outer) published) (newProperty property outer cursor) ∧
      Journal.EntryValues (Function.update (fun index => (entries index).lift) count ⟨some outer,BitVec.ofNat 64 (freshEnd .word cursor 8),oldFlag,oldValue⟩) (count + 1) (newProperty property outer cursor) ∧
      AccountDecode.Registry ready cutoff nextCursor (Function.update (TableFamily.extend objects (Journal.newObject .word cursor 8)) (some outer) published) accounts ∧
      Journal.CounterEffect source ready 1 0 0 ∧
      (∀ query : BitVec 64,query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside (Function.update (TableFamily.extend objects (Journal.newObject .word cursor 8)) (some outer) published) query ∧ ready.memory query = source.memory query) ∧
      TableFamily.Metadata (TableFamily.extend objects (Journal.newObject .word cursor 8)) (Function.update (TableFamily.extend objects (Journal.newObject .word cursor 8)) (some outer) published) ∧
      ready.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      ready.locals = source.locals.update (ofString "inner",.val (.word (BitVec.ofNat 64 cursor))) ∧
      evaluateHOLFiniteState ready allocate = (some (.returned returned),post) := by
  let prelude : ProgHOL 64 := .seq newCall publishCall
  have safeNew : Input.LocalPrefix (ofString "addr") newCall := .call (some (ofString "inner")) _ _ (by
    intro name same
    have nameEq : name = ofString "inner" := Option.some.inj same.symm
    rw [nameEq]
    decide)
  have safePublish : Input.LocalPrefix (ofString "addr") publishCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨ready,prefixRun,tailRun,addressAtReady⟩ := (safeNew.seq safePublish).normal_continue source post allocate returned normal
  have split : ∃ created,evaluateHOLFiniteState source newCall = (none,created) ∧ evaluateHOLFiniteState created publishCall = (none,ready) := by
    rw [evaluateHOLFiniteState_seq_line780] at prefixRun
    cases computed : evaluateHOLFiniteState source newCall with
    | mk result created =>
      cases result with
      | none => exact ⟨created,rfl,by simpa only [computed] using prefixRun⟩
      | some result => simp only [computed] at prefixRun; cases prefixRun
  obtain ⟨created,newRun,publishRun⟩ := split
  have newArgs : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [.const 32#64,.const 8#64] = some (TableRuntime.values .word 8) := rfl
  obtain ⟨newFunded,createdEq,createdFamily,createdImage,createdZone,createdRegistry,createdValues,createdSaved,createdEnvironment,createdGlobals,createdFrame⟩ :=
    TableNewOwnership.assigned_registered source created cursor cutoff 8 3 .word objects outer base cap count entries family image zone countBound environment accounts registry property values savedValues
      (fun pointer => AllocatedBytes.Arena pointer 32 ∧ pointer.toNat % 8 = 0) rfl (by decide) (by decide) (new_code source.code installed) "inner" _ 0#64 innerLocal newArgs newRun
  let createdObjects := TableFamily.extend objects (Journal.newObject .word cursor 8)
  let extendedProperty := newProperty property outer cursor
  have widenedValues : TableFamily.ValuesHave created createdObjects extendedProperty :=
    createdValues.mono created createdObjects _ extendedProperty (fun index value owned => Or.inl owned)
  have widenedSaved : Journal.EntryValues (fun index => (entries index).lift) count extendedProperty :=
    createdSaved.mono _ count _ extendedProperty (fun index value owned => Or.inl owned)
  have createdOuter : created.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)) := by
    rw [createdEq]
    simpa [TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "inner" ≠ ofString "outer" by decide] using outerLocal
  have createdAddress : created.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    rw [createdEq]
    simpa [TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "inner" ≠ ofString "addr" by decide] using addressLocal
  have createdInner : created.locals.lookup (ofString "inner") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
    rw [createdEq]
    exact bind_lookup_same _ _ _
  have createdCode : created.code = source.code := by rw [createdEq]; rfl
  have createdInstalled : Input.OriginalCode.Installed created.code := by rw [createdCode]; exact installed
  have args : evalListHOLFinite created (h := fun query => Classical.propDecidable (created.memaddrs query)) [localVar "outer",localVar "addr",localVar "inner"] =
      some (TableCall.values (createdObjects (some outer)).pointer address (BitVec.ofNat 64 cursor)) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,createdOuter,createdAddress,createdInner,TableCall.values,createdObjects,TableFamily.extend]
  have queryFits : address.toNat + KeyHash.keySize (createdObjects (some outer)).kind < 2^64 := by
    change address.toNat + KeyHash.keySize (objects outer).kind < 2^64
    rw [outerKind]
    change address.toNat + 20 < 2^64
    have := addressArena.upper
    omega
  have queryMapped : ∀ offset < KeyHash.keySize (createdObjects (some outer)).kind,created.memaddrs (panByteAlignHOL (width := 64) (byteAddress address offset)) := by
    change ∀ offset < KeyHash.keySize (objects outer).kind,_
    rw [outerKind]
    intro offset inside
    exact AllocatedBytes.byte_mapped created address 20 offset createdEnvironment.domain addressArena inside
  obtain ⟨room,publishPaid,nextCursor,published,oldFlag,oldValue,publishPositive,publishFunded,publishClock,forward,publishedKind,binary,models,nextImage,nextZone,price,population,nextCounter,
    locals,codes,nextEnvironment,globals,effect,publishFrame,nextValues,nextSaved,nextRegistry,metadata⟩ := Journal.Append.set_call_registered_values created ready (freshEnd .word cursor 8) createdObjects (some outer)
      base cap count (fun index => (entries index).lift) createdFamily createdImage createdZone countBound createdEnvironment cutoff accounts createdRegistry accountApart address (BitVec.ofNat 64 cursor)
      extendedProperty widenedValues (Or.inr ⟨rfl,rfl⟩) widenedSaved queryFits queryMapped (Get.original_code created.code createdInstalled) (AccountSet.journal_code created.code createdInstalled)
      ((createdGlobals (ofString "journal") (by decide)).trans journal) ((createdGlobals (ofString "journal_cap") (by decide)).trans capacity) ((createdGlobals (ofString "journal_n") (by decide)).trans counter)
      _ args publishRun
  have newClock : created.clock = source.clock - (TableRuntime.price 8 + 1) := by rw [createdEq]; rfl
  have totalFunded : TableRuntime.price 8 + 1 + publishPaid ≤ source.clock := by
    rw [newClock] at publishFunded
    calc
      _ ≤ TableRuntime.price 8 + 1 + (source.clock - (TableRuntime.price 8 + 1)) := Nat.add_le_add_left publishFunded _
      _ = source.clock := Nat.add_sub_of_le newFunded
  have totalClock : ready.clock = source.clock - (TableRuntime.price 8 + 1 + publishPaid) := by rw [publishClock,newClock,Nat.sub_sub]
  have totalGlobals : Journal.OtherGlobals source ready := by
    intro name notHeap notCounter
    exact (globals name notHeap notCounter).trans (createdGlobals name notHeap)
  have initialEffect := Journal.CounterEffect.unchanged source created (createdGlobals (ofString "journal_n") (by decide))
  have totalEffect : Journal.CounterEffect source ready 1 0 0 := by simpa only [Nat.zero_add,Nat.add_zero] using initialEffect.trans effect
  have readyLocals : ready.locals = source.locals.update (ofString "inner",.val (.word (BitVec.ofNat 64 cursor))) := by
    rw [locals,createdEq]
    rfl
  change publishPaid + GrowRuntime.growthPotential (objects outer).kind (objects outer).plan.capacity ≤
    Journal.Append.setPrice (objects outer).kind (objects outer).slots.length + 1 + GrowRuntime.growthPotential (objects outer).kind published.plan.capacity at price
  refine ⟨room,TableRuntime.price 8 + 1 + publishPaid,nextCursor,published,oldFlag,oldValue,ready,totalFunded,totalClock,forward,models,nextImage,nextZone,by omega,population,codes.trans createdCode,nextEnvironment,totalGlobals,
    nextValues,nextSaved,nextRegistry,totalEffect,?_,metadata,nextCounter,readyLocals,tailRun⟩
  intro query earlier outside away
  obtain ⟨outsideCreated,sameCreated⟩ := createdFrame query earlier outside
  have before : query.toNat < freshEnd .word cursor 8 := by dsimp only [freshEnd]; omega
  obtain ⟨outsideFinal,sameFinal⟩ := publishFrame.words query before outsideCreated away
  exact ⟨outsideFinal,sameFinal.trans sameCreated⟩

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.new_prefix_normal
