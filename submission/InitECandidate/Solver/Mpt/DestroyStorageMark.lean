import InitECandidate.Solver.Mpt.DestroyStorageGeometry
import InitECandidate.Solver.Mpt.StorageKeyCall
import InitECandidate.Solver.GasBudget.JournalRangeImage
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

theorem mark_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address key value scratch transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
    (writerKind : (objects writer).kind = .storage)
    (addressArena : AllocatedBytes.Arena address 20) (keyArena : AllocatedBytes.Arena key 32) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (slotLocal : source.locals.lookup (ofString "s") = some (Slot.triple 1#64 key value))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (normal : evaluateHOLFiniteState source mark = (none,post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object), paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Journal.Image post (Function.update objects writer next) base count entries ∧
      Journal.Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        13 * (objects writer).slots.length + 29 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧ post.locals = source.locals ∧ post.code = source.code ∧
      WarmKeys.Environment post ∧ HeapGlobals source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧
      AccountDecode.Registry post cutoff nextCursor (Function.update objects writer next) accounts ∧
      TableFamily.PersistentFrame cutoff cursor objects (Function.update objects writer next) source post ∧
      TableFamily.Metadata objects (Function.update objects writer next) := by
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [localVar "addr",.rfield 1 (localVar "s")] = some [.val (.word address),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressLocal,slotLocal,Slot.triple]
  obtain ⟨keyFunded,keyBound,ready,inner,keyLocal,readyLocals,readyClock,readyGlobals,readyCode,readyDomain,readyEndian,
    readyFamily,readyValues,readyRegistry,keyFrame,words,tailRun,scope⟩ := StorageKey.scoped_registered source post address key scratch scratchGlobal
      environment.domain addressArena keyArena scratchArena installed cutoff cursor objects accounts family registry property values floors scratchBelow small
      "k" _ markCall args none (Or.inl rfl) normal
  have readyEnvironment := environment.of_fields readyCode readyDomain readyEndian
  have readyImage : Journal.Image ready objects base count entries := image.of_above
    (by have upper := zone.valid.upper; change base + 32 * cap ≤ 33806089496 at upper; omega) journalAbove readyDomain words
  have readyTransaction : ready.globals.lookup (ofString "ts") = some (.val (.word transaction)) := by rw [readyGlobals]; exact transactionGlobal
  have readyMapped : ready.memaddrs (transaction + 24#64) := by rw [readyDomain]; exact tableMapped
  have readyStored : ready.memory (transaction + 24#64) = .word (objects writer).pointer :=
    (words _ tableAbove).trans tableStored
  have setArgs : evalListHOLFinite ready (h := fun query => Classical.propDecidable (ready.memaddrs query))
      [transactionTable 24#64,localVar "k",.const 1#64] = some (TableCall.values (objects writer).pointer scratch 1#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,transactionTable,localVar,toExact,readyTransaction,keyLocal,valueIsWord,valueWord,
      wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,readyMapped,readyStored,TableCall.values]
  have queryFits : scratch.toNat + KeyHash.keySize (objects writer).kind < 2^64 := by
    rw [writerKind]
    change scratch.toNat + 52 < 2^64
    have upper := scratchArena.upper
    omega
  have queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind,
      ready.memaddrs (panByteAlignHOL (width := 64) (byteAddress scratch offset)) := by
    rw [writerKind]
    intro offset inside
    exact AllocatedBytes.byte_mapped ready scratch 52 offset readyEnvironment.domain scratchArena inside
  obtain ⟨setPaid,nextCursor,next,setFunded,setClock,forward,nextKind,models,nextImage,nextZone,setPrice,population,setLocals,codes,nextEnvironment,globals,
    floorFrame,setFrame,nextValues,metadata⟩ := Journal.set_zone_normal_values ready inner cursor objects writer base cap count entries readyFamily readyImage zone countBound
      readyEnvironment scratch 1#64 property readyValues owned queryFits queryMapped _ setArgs tailRun
  have setRegistry := readyRegistry.framed ready inner cutoff cursor nextCursor objects (Function.update objects writer next) accounts
    ⟨fun query above earlier outside => setFrame.words query (by omega) earlier outside⟩ forward (nextEnvironment.domain.trans readyEnvironment.domain.symm)
  rw [scope]
  let finish := restore source "k" inner
  have finalFamily : TableFamily.Model finish nextCursor (Function.update objects writer next) := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish (Function.update objects writer next) base count entries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := setRegistry.framed inner finish cutoff nextCursor nextCursor (Function.update objects writer next) (Function.update objects writer next) accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor _ inner finish rfl) (Nat.le_refl _) rfl
  have finalLocals : finish.locals = source.locals := by
    have cancel := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.locals) (restore_bound source "k" scratch)
    change HolFiniteMapExact.resVarEq inner.locals (ofString "k",source.locals.lookup (ofString "k")) = _
    rw [setLocals,readyLocals]
    exact cancel
  have finalGlobals : HeapGlobals source finish := by
    intro name other
    exact (globals name other).trans (congrArg (fun map => map.lookup name) readyGlobals)
  have persistent : TableFamily.PersistentFrame cutoff cursor objects (Function.update objects writer next) source finish :=
    keyFrame.trans ⟨fun query above earlier outside => setFrame.words query (by omega) earlier outside⟩ (Nat.le_refl _)
  rw [writerKind] at setPrice
  have keyPaid := StorageKey.price_bound address key scratch
  refine ⟨StorageKey.price address key scratch + 1 + setPaid,nextCursor,next,by omega,by change inner.clock = _; omega,forward,
    finalFamily,finalImage,nextZone,?_,population,finalLocals,codes.trans readyCode,nextEnvironment.of_fields rfl rfl rfl,finalGlobals,
    nextValues,finalRegistry,persistent,metadata⟩
  rw [writerKind]
  rw [mark_price] at setPrice
  omega

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.mark_normal
