import InitECandidate.Solver.Mpt.WsAccountOptionalFamilyFrame
import InitECandidate.Solver.Mpt.WsAccountOptionalRoom
import InitECandidate.Solver.Mpt.WsAccountWorldAgreement
import InitECandidate.Solver.WitnessRadix.Keccak256EnvironmentFields

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix MutableTable

/-- Complete actual original provider from current immutable witness,
scratch/query ownership and live table family. The real normal allocator
derives output room before low-level hash/lookup models are constructed.
Both witness and table models are reconstructed afterward from actual
memory frames; the source price is independent of witness leaf size. -/
theorem body_world_family {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit)
    (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0) (queryArena : AllocatedBytes.Arena addr 20)
    (stateBelow : stp.toNat+200≤cutoff) (padBelow : pad.toNat+136≤cutoff)
    (objects : ι → TableFamily.Object) (family : TableFamily.Model source heap.toNat objects) (floors : ∀ index,frozenEnd≤(objects index).floor)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0) (afterWorld : frozenEnd≤heap.toNat)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ nextCursor,(nextCursor=heap.toNat ∨ nextCursor=heap.toNat+120) ∧ TableFamily.Model post nextCursor objects ∧
      Nonempty (WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit) ∧ Keccak256.Environment post stp pad ∧
      Result post heap cursor limit returned ∧ HeapGlobals source post ∧ source.clock-post.clock≤31051 ∧
      (returned=.val (.word 1#64) ∨ Nonempty (AccountDecode.Image post heap)) := by
  have room := body_room source post addr heap addressCell heapGlobal heapBound installed returned normal
  have outputArena : AllocatedBytes.Arena heap 32 := ⟨by have := world.nibsArena.lower; have := world.nibsBelow; have := world.ordered; omega,room⟩
  let data := world.data source ws root nibs heap cutoff frozenEnd valueLimit afterWorld outputArena
  let values := world.values_at_heap source ws root nibs heap cutoff frozenEnd valueLimit afterWorld
  have valueProtection := world.value_protected source ws root nibs cutoff frozenEnd valueLimit
  obtain ⟨graphProtection,valuesProtection,rootProtection⟩ := world.protections source ws root nibs heap stp pad cutoff frozenEnd valueLimit afterWorld heapBound heapAligned stateBelow padBelow
  have hashData := Keccak256.allocated_entry source stp addr pad heap 20 environment ⟨stateArena,stateAligned,queryArena,padArena,padAligned,outputArena⟩
  obtain ⟨result,nonheap,price,image,memory⟩ := body_image source post ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash cutoff valueLimit
    data values valueProtection hashData graphProtection valuesProtection rootProtection addressCell arena heapGlobal heapBound outputArena.lower heapAligned sizeBound aligned scratchBelow
    rootGlobal hashGlobal rootArena hashArena installed returned normal
  have fields := Input.evaluation_fields source post body _ normal
  have separation : FamilySeparated objects cutoff stp pad nibs := by
    intro index
    have := floors index
    have := world.ordered
    have := world.nibsBelow
    exact ⟨by omega,by omega,by omega,by omega⟩
  obtain ⟨nextCursor,choice,nextFamily⟩ := result.family source post heap cursor limit stp pad nibs cutoff objects family separation heapBound heapAligned scratchBelow fields.1 fields.2.1 returned memory
  have small : cutoff<2^64 := by have := world.ordered; have := world.bounded; omega
  have agree (query : BitVec 64) (needed : world.graph.Footprint query ∨ Mpt.TrieWalk.ValueFootprint world.graph query ∨ query=ws+24#64) : post.memory query=source.memory query := by
    have span := world.footprint query needed
    have guarded : Keccak256.Protected stp pad heap query := by
      rcases needed with structureWord | valueWord | rootWord
      · exact graphProtection query structureWord
      · exact valuesProtection query valueWord
      · rw [rootWord]; exact rootProtection
    exact memory query (by omega) (by omega) guarded
      (by intro offset active; exact (CopyGeneral.Away.before nibs query 64 cutoff world.nibsBelow small span.1 offset active).2)
  let nextWorld := world.of_agreement source post ws root nibs cutoff frozenEnd valueLimit fields.1 fields.2.1
    (nonheap _ (by decide)) (nonheap _ (by decide)) agree
  have nextEnvironment := environment.after_execution source post stp pad body _ normal nonheap
  exact ⟨nextCursor,choice,nextFamily,⟨nextWorld⟩,nextEnvironment,result,nonheap,price,image⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_world_family
