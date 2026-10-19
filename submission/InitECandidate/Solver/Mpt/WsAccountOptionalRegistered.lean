import InitECandidate.Solver.Mpt.WsAccountOptionalWorld
import InitECandidate.Solver.Mpt.AccountRegistryAppend

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix MutableTable

/-- Actual normal provider retains all old registered accounts and adds
exactly its real fresh account on a hit. The returned sentinel/pointer,
retained cursor, registry and known-value weakening are derived together. -/
theorem body_registered {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit)
    (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0) (queryArena : AllocatedBytes.Arena addr 20)
    (stateBelow : stp.toNat+200≤cutoff) (padBelow : pad.toNat+136≤cutoff)
    (objects : ι → TableFamily.Object) (anchor : ι) (accounts : List (BitVec 64))
    (registry : AccountDecode.Registry source cutoff heap.toNat objects accounts)
    (family : TableFamily.Model source heap.toNat objects) (floors : ∀ index,frozenEnd≤(objects index).floor)
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
    ∃ nextCursor nextAccounts,
      ((nextAccounts=accounts ∧ returned=.val (.word 1#64)) ∨ (nextAccounts=accounts++[heap] ∧ returned=.val (.word heap))) ∧
      TableFamily.Model post nextCursor objects ∧ AccountDecode.Registry post cutoff nextCursor objects nextAccounts ∧
      Nonempty (WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit) ∧ Keccak256.Environment post stp pad ∧
      Result post heap cursor limit returned ∧ HeapGlobals source post ∧ source.clock-post.clock≤31051 ∧
      (∀ value : BitVec 64,AccountDecode.Registry.Known accounts value → AccountDecode.Registry.Known nextAccounts value) ∧
      (∀ query : BitVec 64,cutoff≤query.toNat → query.toNat<heap.toNat → post.memory query=source.memory query) ∧ (nextCursor=heap.toNat ∨ nextCursor=heap.toNat+120) := by
  obtain ⟨nextCursor,choice,nextFamily,nextWorld,nextEnvironment,result,globals,frame,beforeMemory,price,image⟩ :=
    body_world_family source post ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash cutoff frozenEnd valueLimit world environment
      stateArena stateAligned padArena padAligned queryArena stateBelow padBelow objects family floors addressCell arena heapGlobal heapBound heapAligned afterWorld
      sizeBound aligned scratchBelow rootGlobal hashGlobal rootArena hashArena installed returned normal
  have fields := Input.evaluation_fields source post body _ normal
  have retained := registry.framed source post cutoff heap.toNat heap.toNat objects objects accounts frame (Nat.le_refl _) fields.1
  have nextTable := nextFamily.tables anchor
  have nextNumber : (BitVec.ofNat 64 nextCursor).toNat=nextCursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := nextTable.bounded; omega)]
  have actualCursor (word : BitVec 64) (binding : post.globals.lookup (ofString "heap_ptr")=some (.val (.word word))) : nextCursor=word.toNat := by
    have equal := Option.some.inj (nextTable.heap.symm.trans binding)
    have words : BitVec.ofNat 64 nextCursor=word := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
    have number := congrArg BitVec.toNat words
    rw [nextNumber] at number
    exact number
  rcases result.2 with absent | present
  · have cursorEq := actualCursor heap absent.2
    have registered : AccountDecode.Registry post cutoff nextCursor objects accounts := by rw [cursorEq]; exact retained
    exact ⟨nextCursor,accounts,Or.inl ⟨rfl,absent.1⟩,nextFamily,registered,nextWorld,nextEnvironment,result,globals,price,
      fun value owned=>owned,beforeMemory,Or.inl cursorEq⟩
  · have cursorWord := actualCursor (heap+120#64) present.2.1
    have room := present.2.2
    have cursorEq : nextCursor=heap.toNat+120 := by
      rw [BitVec.toNat_add_of_lt (by change heap.toNat+120<2^64; omega)] at cursorWord
      exact cursorWord
    have actualImage : Nonempty (AccountDecode.Image post heap) := by
      rcases image with absentImage | image
      · have words : heap=1#64 := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using present.1.symm.trans absentImage
        have number := congrArg BitVec.toNat words
        change heap.toNat=1 at number
        have := world.nibsArena.lower
        have := world.nibsBelow
        have := world.ordered
        omega
      · exact image
    obtain ⟨accountImage⟩ := actualImage
    have outside := AccountDecode.Registry.fresh_references source heap.toNat objects family heap (Nat.le_refl _) accountImage.output
    have registered := retained.append post cutoff heap.toNat nextCursor objects accounts heap accountImage (Nat.le_refl _)
      (by have := world.ordered; omega) (by rw [cursorEq]; omega) outside
    exact ⟨nextCursor,accounts++[heap],Or.inr ⟨rfl,present.1⟩,nextFamily,registered,nextWorld,nextEnvironment,result,globals,price,
      fun value owned=>AccountDecode.Registry.known_append accounts heap value owned,beforeMemory,Or.inr cursorEq⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_registered
