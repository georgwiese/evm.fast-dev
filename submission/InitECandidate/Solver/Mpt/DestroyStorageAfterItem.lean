import InitECandidate.Solver.Mpt.DestroyStorageMark
import InitECandidate.Solver.Input.ControlContinue

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

theorem after_item_normal {ι : Type} [DecidableEq ι]
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
    (index : Nat) (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (normal : evaluateHOLFiniteState source afterItem = (none,post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object), paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Journal.Image post (Function.update objects writer next) base count entries ∧
      Journal.Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        13 * (objects writer).slots.length + 29 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧ post.locals = (bind source "i" (BitVec.ofNat 64 (index + 1))).locals ∧ post.code = source.code ∧
      WarmKeys.Environment post ∧ HeapGlobals source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧
      AccountDecode.Registry post cutoff nextCursor (Function.update objects writer next) accounts ∧
      TableFamily.PersistentFrame cutoff cursor objects (Function.update objects writer next) source post ∧
      TableFamily.Metadata objects (Function.update objects writer next) := by
  rw [after_item_dispatch source key value slotLocal] at normal
  have safe : Input.LocalPrefix (ofString "i") mark := by
    unfold mark markCall
    exact .decCall _ _ _ _ (by decide) (.call none _ _ (by intro name impossible; cases impossible))
  obtain ⟨marked,markedRun,incrementRun,keepI⟩ := safe.control_continue source post increment none .next normal
  obtain ⟨paid,nextCursor,next,funded,clock,forward,models,nextImage,nextZone,price,population,locals,codes,nextEnvironment,globals,
    nextValues,nextRegistry,frame,metadata⟩ := mark_normal source marked address key value scratch transaction cursor cutoff objects writer base cap count entries
      family image zone countBound environment installed accounts registry property values owned writerKind addressArena keyArena scratchArena floors scratchBelow small journalAbove
      addressLocal slotLocal scratchGlobal transactionGlobal tableMapped tableStored tableAbove markedRun
  have actual := increment_execute marked index (keepI.trans indexLocal)
  have postEq := congrArg Prod.snd (incrementRun.symm.trans actual)
  change post = bind marked "i" (BitVec.ofNat 64 (index + 1)) at postEq
  subst post
  let finish := bind marked "i" (BitVec.ofNat 64 (index + 1))
  have finalFamily : TableFamily.Model finish nextCursor (Function.update objects writer next) := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish (Function.update objects writer next) base count entries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed marked finish cutoff nextCursor nextCursor (Function.update objects writer next) (Function.update objects writer next) accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor _ marked finish rfl) (Nat.le_refl _) rfl
  have finalLocals : finish.locals = (bind source "i" (BitVec.ofNat 64 (index + 1))).locals := by
    change marked.locals.update _ = source.locals.update _
    rw [locals]
  exact ⟨paid,nextCursor,next,funded,clock,forward,finalFamily,finalImage,nextZone,price,population,finalLocals,codes,
    nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,finalRegistry,⟨frame.words⟩,metadata⟩

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.after_item_normal
