import InitECandidate.Solver.Mpt.WsAccountOptionalTailNormal
import InitECandidate.Solver.Mpt.AccountDecodeCallImage

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Real decoder/return suffix retains the produced physical account and
all ordinary words outside its two actual write regions above scratch. -/
theorem after_alloc_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out emptyRoot emptyHash : BitVec 64) (cutoff : Nat)
    (leafCell : source.locals.lookup (ofString "leaf")=some (TrieWalk.triple 1#64 pointer length))
    (outputCell : source.locals.lookup (ofString "a")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (output : AccountDecode.Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) :
    Nonempty (AccountDecode.Image post out) ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat →
        query.toNat<out.toNat ∨ out.toNat+56≤query.toNat → post.memory query=source.memory query) := by
  rw [after_alloc_shape] at normal
  have safe : Input.LocalPrefix (ofString "a") decode := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,decoded,tailRun,outputEq⟩ := safe.normal_continue source post (.return (localVar "a")) returned normal
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) decodeArguments=some (AccountDecode.values pointer length out) := by
    simp [decodeArguments,field,AccountDecode.values,TrieWalk.triple,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leafCell,outputCell]
  obtain ⟨positive,⟨image⟩,nextArena,nextHeap,room,nonheap,window,price⟩ := AccountDecode.ignored_image source middle pointer length heap cursor limit out emptyRoot emptyHash cutoff
    arena heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove rootGlobal hashGlobal rootArena hashArena output installed decodeArguments args decoded
  have actual := Input.return_normal middle post (localVar "a") returned tailRun
  rw [actual.2]
  exact ⟨⟨AccountDecode.Image.of_agreement middle _ out image rfl (by rfl) (by rfl)⟩,window⟩

set_option maxRecDepth 10000 in
/-- A present normal provider suffix constructs the actual account image
and preserves every pre-existing persistent word above its scratch cursor.
The original allocator's room and reached state are derived from execution. -/
theorem after_guard_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit emptyRoot emptyHash : BitVec 64) (cutoff : Nat)
    (leafCell : source.locals.lookup (ofString "leaf")=some (TrieWalk.triple 1#64 pointer length))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterGuard=(some (.returned returned),post)) :
    Nonempty (AccountDecode.Image post heap) ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat → post.memory query=source.memory query) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 56#64]=some (PersistentAlloc.values 56#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,positive,inner,tailRun,restored⟩ := PersistentAlloc.call_normal source post "a" [.const 56#64] afterAlloc heap 56#64 args
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapGlobal heapBound returned
    (by rw [←after_guard_shape]; exact normal)
  let ready := bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 56#64) "a" heap
  have currentLeaf : ready.locals.lookup (ofString "leaf")=some (TrieWalk.triple 1#64 pointer length) :=
    (bind_lookup_other _ "a" "leaf" heap (by decide)).trans leafCell
  have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))).lookup (ofString "heap_ptr")=_
    simp [HolFiniteMapExact.update,FUPDATE]
  have currentArena := Rlp.Validation.Arena.heap_updated source ready cursor limit (PersistentAlloc.rounded heap 56#64) arena rfl rfl
  have nonheap : HeapGlobals source ready := HeapGlobals.update source (PersistentAlloc.rounded heap 56#64)
  have guards := PersistentAlloc.guards heap 56#64 room
  have output : AccountDecode.Output heap := ⟨heapLower,room,heapAligned⟩
  obtain ⟨⟨image⟩,window⟩ := after_alloc_image ready inner pointer length (PersistentAlloc.rounded heap 56#64) cursor limit heap emptyRoot emptyHash cutoff
    currentLeaf (bind_lookup_same _ _ _) currentArena currentHeap guards.2.2.2.1 (by have := guards.2.2.1; change heap.toNat+56≤_ at this; omega)
    sizeBound aligned scratchBelow inputAbove ((nonheap _ (by decide)).trans rootGlobal) ((nonheap _ (by decide)).trans hashGlobal)
    rootArena hashArena output installed returned tailRun
  rw [restored]
  refine ⟨⟨AccountDecode.Image.of_agreement inner _ heap image rfl (by rfl) (by rfl)⟩,?_⟩
  intro query beyond below
  exact window query beyond (Or.inl (by have := guards.2.2.1; change heap.toNat+56≤_ at this; omega)) (Or.inl below)

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_alloc_image
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_guard_image
