import InitECandidate.Solver.Mpt.WsAccountOptionalRegistered
import InitECandidate.Solver.MutableTable.FamilyValueRange

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix MutableTable

/-- The complete real provider preserves every occupied cache value and
returns a sentinel or an account in the actual post-execution registry. -/
theorem body_registered_values {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit)
    (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0) (queryArena : AllocatedBytes.Arena addr 20)
    (stateBelow : stp.toNat+200≤cutoff) (padBelow : pad.toNat+136≤cutoff)
    (objects : ι → TableFamily.Object) (anchor : ι) (accounts : List (BitVec 64))
    (registry : AccountDecode.Registry source cutoff heap.toNat objects accounts)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property)
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
      (∀ query : BitVec 64,cutoff≤query.toNat → query.toNat<heap.toNat → post.memory query=source.memory query) ∧
      TableFamily.ValuesHave post objects property ∧
      (∃ value : BitVec 64,returned=.val (.word value) ∧ AccountDecode.Registry.Known nextAccounts value) ∧ (nextCursor=heap.toNat ∨ nextCursor=heap.toNat+120) := by
  obtain ⟨nextCursor,nextAccounts,shape,nextFamily,nextRegistry,nextWorld,nextEnvironment,result,globals,price,weakening,beforeMemory,choice⟩ :=
    body_registered source post ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash cutoff frozenEnd valueLimit world environment
      stateArena stateAligned padArena padAligned queryArena stateBelow padBelow objects anchor accounts registry family floors addressCell arena heapGlobal heapBound heapAligned afterWorld
      sizeBound aligned scratchBelow rootGlobal hashGlobal rootArena hashArena installed returned normal
  have nextValues := tableValues.of_range source post cutoff heap.toNat objects property family
    (fun index=>Nat.le_trans world.ordered (floors index)) beforeMemory
  have returnedOwned : ∃ value : BitVec 64,returned=.val (.word value) ∧ AccountDecode.Registry.Known nextAccounts value := by
    rcases shape with ⟨same,absent⟩ | ⟨added,present⟩
    · exact ⟨1#64,absent,Or.inl rfl⟩
    · refine ⟨heap,present,Or.inr ?_⟩
      rw [added]
      simp
  exact ⟨nextCursor,nextAccounts,shape,nextFamily,nextRegistry,nextWorld,nextEnvironment,result,globals,price,weakening,beforeMemory,nextValues,returnedOwned,choice⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_registered_values
