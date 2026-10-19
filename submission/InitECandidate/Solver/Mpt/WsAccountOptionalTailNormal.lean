import InitECandidate.Solver.Mpt.WsAccountOptionalTailCost
import InitECandidate.Solver.Mpt.AccountDecodeCallNormal

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_alloc_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out : BitVec 64) (cutoff : Nat)
    (leafCell : source.locals.lookup (ofString "leaf")=some (TrieWalk.triple 1#64 pointer length))
    (outputCell : source.locals.lookup (ofString "a")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : AccountDecode.Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) :
    returned=.val (.word out) ∧ Rlp.Validation.Arena post cursor limit ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))) ∧ heap.toNat+64≤33806089496 := by
  rw [after_alloc_shape] at normal
  have safe : Input.LocalPrefix (ofString "a") decode := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,decoded,tailRun,outputEq⟩ := safe.normal_continue source post (.return (localVar "a")) returned normal
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) decodeArguments=some (AccountDecode.values pointer length out) := by
    simp [decodeArguments,field,AccountDecode.values,TrieWalk.triple,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leafCell,outputCell]
  obtain ⟨positive,nextArena,nextHeap,room,bounded⟩ := AccountDecode.ignored_cursors source middle pointer length heap cursor limit out cutoff
    arena heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove output installed decodeArguments args decoded
  have actual := Input.return_normal middle post (localVar "a") returned tailRun
  have currentOutput := outputEq.trans outputCell
  have read : eval middle (localVar "a")=some (.val (.word out)) := by simp [eval,localVar,evalHOLExact,toExact,currentOutput]
  have returnedEq := Option.some.inj (actual.1.symm.trans read)
  rw [actual.2]
  exact ⟨returnedEq,Rlp.Validation.Arena.of_fields middle _ cursor limit nextArena rfl rfl,nextHeap,room⟩

set_option maxRecDepth 10000 in
/-- Real normal provider allocation/decoder suffix returns the actual
account pointer and reserves56+64=120 bytes for an aligned incoming heap.
Both allocator room checks and the count-four fact come from execution. -/
theorem after_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (leafCell : source.locals.lookup (ofString "leaf")=some (TrieWalk.triple 1#64 pointer length))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterGuard=(some (.returned returned),post)) :
    returned=.val (.word heap) ∧ Rlp.Validation.Arena post cursor limit ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (heap+120#64))) ∧ heap.toNat+120≤33806089496 := by
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
  have guards := PersistentAlloc.guards heap 56#64 room
  have output : AccountDecode.Output heap := ⟨heapLower,room,heapAligned⟩
  obtain ⟨returnedEq,nextArena,nextHeap,recordRoom⟩ := after_alloc_normal ready inner pointer length (PersistentAlloc.rounded heap 56#64) cursor limit heap cutoff
    currentLeaf (bind_lookup_same _ _ _) currentArena currentHeap guards.2.2.2.1 (by have := guards.2.2.1; change heap.toNat+56≤_ at this; omega)
    sizeBound aligned scratchBelow inputAbove output installed returned tailRun
  have firstNumber : (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 := by
    rw [PersistentAlloc.rounded_nat heap 56#64 (by change heap.toNat+56+7<2^64; omega)]
    change (heap.toNat+56+7)/8*8=heap.toNat+56
    omega
  have totalRoom : heap.toNat+120≤33806089496 := by rw [firstNumber] at recordRoom; omega
  have secondNumber : (PersistentAlloc.rounded (PersistentAlloc.rounded heap 56#64) 64#64).toNat=heap.toNat+120 := by
    rw [PersistentAlloc.rounded_nat _ 64#64 (by rw [firstNumber]; change heap.toNat+56+64+7<2^64; omega),firstNumber]
    change (heap.toNat+56+64+7)/8*8=heap.toNat+120
    omega
  have finalHeap : PersistentAlloc.rounded (PersistentAlloc.rounded heap 56#64) 64#64=heap+120#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [secondNumber,BitVec.toNat_add_of_lt (by change heap.toNat+120<2^64; omega)]
    rfl
  rw [restored]
  exact ⟨returnedEq,Rlp.Validation.Arena.of_fields inner _ cursor limit nextArena rfl rfl,by rwa [finalHeap] at nextHeap,totalRoom⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_alloc_normal
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_guard_normal
