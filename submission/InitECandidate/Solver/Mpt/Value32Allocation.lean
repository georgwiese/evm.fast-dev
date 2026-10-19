import InitECandidate.Solver.Mpt.Value32Memory
import InitECandidate.Solver.WitnessRadix.AllocationNormalExpected
import InitECandidate.Solver.GasBudget.WarmKeysInvariant
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.Value32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem prefix_normal {ι : Type}
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff : Nat)
    (objects : ι → TableFamily.Object) (writer : ι) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (image : Journal.Image source objects base count entries) (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (words : Input.RlpWrite.U256Value.Words)
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString "v") .one (ofString "alloc") [.const 32#64]
      (.seq (.store (localVar "v") (localVar "value")) continuation)) = (some (.returned returned),post)) :
    cursor + 32 ≤ 33806089496 ∧ 1 ≤ source.clock ∧ AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 32 ∧ (BitVec.ofNat 64 cursor).toNat % 8 = 0 ∧
      TableFamily.Model (stored source cursor words) (cursor + 32) objects ∧ Journal.Image (stored source cursor words) objects base count entries ∧
      Journal.Zone objects base cap (cursor + 32) ∧ AccountDecode.Registry (stored source cursor words) cutoff (cursor + 32) objects accounts ∧
      TableFamily.ValuesHave (stored source cursor words) objects property ∧ TableFamily.PersistentFrame 0 cursor objects objects source (stored source cursor words) ∧
      HeapGlobals source (stored source cursor words) ∧ ∃ finish,
        evaluateHOLFiniteState (stored source cursor words) continuation = (some (.returned returned),finish) ∧ post = restore source "v" finish := by
  have table := family.tables writer
  have aligned : (cursor + 32) % 8 = 0 := by have := table.aligned; omega
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [.const 32#64] = some (PersistentAlloc.values 32#64) := rfl
  obtain ⟨room,nextBound,positive,inner,afterAlloc,restored⟩ := PersistentAlloc.call_normal_expected source post "v" [.const 32#64]
    (.seq (.store (localVar "v") (localVar "value")) continuation) cursor 32 (cursor + 32) table.bounded (by decide) (Nat.le_refl _) (by omega) aligned args
    environment.allocCode environment.trapCode table.heap returned normal
  obtain ⟨models,nextImage,nextZone,nextRegistry,nextValues,frame,globals,arena,pointerAligned⟩ := stored_models source cursor cutoff objects writer accounts family registry
    property values base cap count entries image zone countBound words room
  let ready := allocated source cursor
  have pointerLocal : ready.locals.lookup (ofString "v") = some (.val (.word (BitVec.ofNat 64 cursor))) := bind_lookup_same _ _ _
  have readyValue : ready.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words) := by
    simpa [ready,allocated,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "v" ≠ ofString "value" from by decide] using valueLocal
  have destinationRead : eval ready (localVar "v") = some (.val (.word (BitVec.ofNat 64 cursor))) := by simp [eval,localVar,evalHOLExact,toExact,pointerLocal]
  have valueRead : eval ready (localVar "value") = some (Input.RlpWrite.U256Value.tuple words) := by simp [eval,localVar,evalHOLExact,toExact,readyValue]
  have mapped (index : Fin 4) : ready.memaddrs (BitVec.ofNat 64 cursor + BitVec.ofNat 64 (8 * index.val)) := by
    have bound := index.isLt
    exact AllocatedBytes.word_mapped ready (BitVec.ofNat 64 cursor) 32 (8 * index.val) environment.domain arena (by omega) pointerAligned (by omega)
  have safe : Input.LocalPrefix (ofString "value") (.store (localVar "v") (localVar "value")) := .store _ _
  obtain ⟨written,storeRun,tailRun,keepValue⟩ := safe.normal_continue ready inner continuation returned afterAlloc
  have actual := Input.RlpWrite.U256Value.store_execute ready (localVar "v") (localVar "value") (BitVec.ofNat 64 cursor) words destinationRead valueRead mapped
  have same := congrArg Prod.snd (storeRun.symm.trans actual)
  change written = stored source cursor words at same
  rw [same] at tailRun
  exact ⟨room,positive,arena,pointerAligned,models,nextImage,nextZone,nextRegistry,nextValues,frame,globals,inner,tailRun,restored⟩

end InitECandidate.Solver.Mpt.Value32

#print axioms InitECandidate.Solver.Mpt.Value32.prefix_normal
