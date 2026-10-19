import InitECandidate.Solver.Mpt.DestroyStorageAfterItem
import InitECandidate.Solver.Input.ScopeLookup

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem body_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address scratch transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer reader : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
    (writerKind : (objects writer).kind = .storage) (readerKind : (objects reader).kind = .word)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (readerLocal : source.locals.lookup (ofString "inner") = some (.val (.word (objects reader).pointer)))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (index : Fin (objects reader).slots.length) (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index.val))))
    (normal : evaluateHOLFiniteState source loopBody = (none,post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object), paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Journal.Image post (Function.update objects writer next) base count entries ∧
      Journal.Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        13 * (objects writer).slots.length + 31 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧ post.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index.val + 1)))) ∧ post.code = source.code ∧
      WarmKeys.Environment post ∧ HeapGlobals source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧
      AccountDecode.Registry post cutoff nextCursor (Function.update objects writer next) accounts ∧
      TableFamily.PersistentFrame cutoff cursor objects (Function.update objects writer next) source post ∧
      TableFamily.Metadata objects (Function.update objects writer next) := by
  have table := family.tables reader
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [localVar "inner",localVar "i"] = some (ReadCall.values (objects reader).pointer (BitVec.ofNat 64 index.val)) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,readerLocal,indexLocal,ReadCall.values]
  obtain ⟨itemFunded,value,inner,tailRun,scope⟩ := Item.scoped_normal source post (objects reader).kind (objects reader).plan table.valid
    environment.domain (objects reader).slots table.occupied table.header index installed "s" _ afterItem args none (Or.inl rfl) normal
  let selectedKey := cell (objects reader).plan .keys 0 + BitVec.ofNat 64 ((objects reader).slots.get index) * BitVec.ofNat 64 (stride (objects reader).kind)
  let ready := setVarHOLFinite (ofString "s") (Slot.triple 1#64 selectedKey value) {source with clock := source.clock - 2}
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "s" ≠ ofString "addr" from by decide] using addressLocal
  have readyIndex : ready.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index.val))) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "s" ≠ ofString "i" from by decide] using indexLocal
  have slotLocal : ready.locals.lookup (ofString "s") = some (Slot.triple 1#64 selectedKey value) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have wordValid : Valid .word (objects reader).plan := by rw [← readerKind]; exact table.valid
  have keyArena : AllocatedBytes.Arena selectedKey 32 := by
    have selected := selected_key_arena (objects reader).plan wordValid ((objects reader).slots.get index)
      (table.occupied.inside _ (List.get_mem (objects reader).slots index))
    simpa [selectedKey,readerKind] using selected
  obtain ⟨paid,nextCursor,next,funded,clock,forward,models,nextImage,nextZone,price,population,locals,codes,nextEnvironment,globals,
    nextValues,nextRegistry,frame,metadata⟩ := after_item_normal ready inner address selectedKey value scratch transaction cursor cutoff objects writer base cap count entries
      readyFamily readyImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts readyRegistry property values owned writerKind
      addressArena keyArena scratchArena floors scratchBelow small journalAbove readyAddress slotLocal scratchGlobal transactionGlobal tableMapped tableStored tableAbove
      index.val readyIndex tailRun
  rw [scope]
  let finish := restore source "s" inner
  have finalFamily : TableFamily.Model finish nextCursor (Function.update objects writer next) := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish (Function.update objects writer next) base count entries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed inner finish cutoff nextCursor nextCursor (Function.update objects writer next) (Function.update objects writer next) accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor _ inner finish rfl) (Nat.le_refl _) rfl
  have finalIndex : finish.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index.val + 1)))) := by
    rw [Input.ScalarScope.restore_other source inner "s" "i" (by decide),locals]
    simp [QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  change paid ≤ source.clock - 2 at funded
  change inner.clock = source.clock - 2 - paid at clock
  exact ⟨2 + paid,nextCursor,next,by omega,by change inner.clock = _; omega,forward,finalFamily,finalImage,nextZone,by omega,population,
    finalIndex,codes,nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,finalRegistry,⟨frame.words⟩,metadata⟩

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.body_normal
