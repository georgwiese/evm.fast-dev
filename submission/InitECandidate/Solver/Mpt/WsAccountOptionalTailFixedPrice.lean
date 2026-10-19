import InitECandidate.Solver.Mpt.WsAccountOptionalTailNormal
import InitECandidate.Solver.Mpt.AccountDecodeCallLeafSize
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The genuine successful decoder/return suffix has a fixed source price
because its actual account leaf has at most149 bytes. -/
theorem after_alloc_fixed_price (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out emptyRoot emptyHash : BitVec 64) (cutoff : Nat)
    (leafCell : source.locals.lookup (ofString "leaf")=some (TrieWalk.triple 1#64 pointer length))
    (outputCell : source.locals.lookup (ofString "a")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (output : AccountDecode.Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) : source.clock-post.clock≤28752 := by
  rw [after_alloc_shape] at normal
  have safe : Input.LocalPrefix (ofString "a") decode := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,decoded,tailRun,outputEq⟩ := safe.normal_continue source post (.return (localVar "a")) returned normal
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) decodeArguments=some (AccountDecode.values pointer length out) := by
    simp [decodeArguments,field,AccountDecode.values,TrieWalk.triple,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leafCell,outputCell]
  obtain ⟨small,price⟩ := AccountDecode.ignored_leaf_size source middle pointer length heap cursor limit out emptyRoot emptyHash cutoff
    arena heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove rootGlobal hashGlobal output installed decodeArguments args decoded
  rw [(Input.return_normal middle post (localVar "a") returned tailRun).2]
  exact price

/-- The real56-byte normal allocator adds exactly one caller tick before
the successful account decoder suffix. Its room is derived from execution. -/
theorem after_guard_fixed_price (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit emptyRoot emptyHash : BitVec 64) (cutoff : Nat)
    (leafCell : source.locals.lookup (ofString "leaf")=some (TrieWalk.triple 1#64 pointer length))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterGuard=(some (.returned returned),post)) : source.clock-post.clock≤28753 := by
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
  have price := after_alloc_fixed_price ready inner pointer length (PersistentAlloc.rounded heap 56#64) cursor limit heap emptyRoot emptyHash cutoff
    currentLeaf (bind_lookup_same _ _ _) currentArena currentHeap guards.2.2.2.1 (by have := guards.2.2.1; change heap.toNat+56≤_ at this; omega)
    sizeBound aligned scratchBelow inputAbove ((nonheap _ (by decide)).trans rootGlobal) ((nonheap _ (by decide)).trans hashGlobal)
    output installed returned tailRun
  have clock := evaluateHOLFiniteState_clock_le ready afterAlloc
  rw [tailRun] at clock
  change inner.clock≤source.clock-1 at clock
  change source.clock-1-inner.clock≤28752 at price
  rw [restored]
  change source.clock-inner.clock≤28753
  omega

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_alloc_fixed_price
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_guard_fixed_price
