import InitECandidate.Solver.Mpt.AccountNewTail
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.AccountNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Input.RlpWrite

/-- A successful original constructor derives56-byte allocation room and
its exact source price. The resulting account and complete earlier-word
frame follow from the actual allocator and seven original word writes. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nonce : BitVec 64) (balance : U256Value.Words) (root hash : BitVec 64)
    (nonceCell : source.locals.lookup (ofString "nonce")=some (.val (.word nonce)))
    (balanceCell : source.locals.lookup (ofString "balance")=some (U256Value.tuple balance))
    (hashCell : source.locals.lookup (ofString "code_hash")=some (.val (.word hash)))
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    1≤source.clock ∧ heap.toNat+56≤33806089496 ∧ returned=.val (.word heap) ∧ post.clock=source.clock-1 ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
        memory:=finalMemory source.memory heap nonce balance root hash,clock:=source.clock-1} ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧
      Nonempty (AccountDecode.Image post heap) ∧ Rlp.Slices.Window source post heap.toNat (heap.toNat+56) ∧
      HeapGlobals source post ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 56#64]=some (PersistentAlloc.values 56#64) := rfl
  rw [body_shape] at normal
  obtain ⟨room,positive,inner,tailRun,restored⟩ := PersistentAlloc.call_normal source post "a" [.const 56#64] tail heap 56#64 args
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapGlobal heapBound returned normal
  change heap.toNat+56≤33806089496 at room
  let allocated := PersistentAlloc.post {source with clock:=source.clock-1} heap 56#64
  let ready := bind allocated "a" heap
  have nextNonce : ready.locals.lookup (ofString "nonce")=some (.val (.word nonce)) :=
    (bind_lookup_other allocated "a" "nonce" heap (by decide)).trans nonceCell
  have nextBalance : ready.locals.lookup (ofString "balance")=some (U256Value.tuple balance) :=
    (bind_lookup_other allocated "a" "balance" heap (by decide)).trans balanceCell
  have nextHash : ready.locals.lookup (ofString "code_hash")=some (.val (.word hash)) :=
    (bind_lookup_other allocated "a" "code_hash" heap (by decide)).trans hashCell
  have nextRoot : ready.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)) :=
    (HeapGlobals.update source (PersistentAlloc.rounded heap 56#64) (ofString "empty_trie_root") (by decide)).trans rootGlobal
  have output : AccountDecode.Output heap := ⟨heapLower,room,heapAligned⟩
  obtain ⟨actual,⟨image⟩,window⟩ := tail_execute ready heap nonce balance root hash (bind_lookup_same allocated "a" heap)
    nextNonce nextBalance nextHash nextRoot output domain rootArena hashArena
  have same := tailRun.symm.trans actual
  have returnedEq : returned=.val (.word heap) := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst same
  have innerEq := congrArg Prod.snd same
  change inner=tailTarget ready heap nonce balance root hash at innerEq
  have postEq : post=restore source "a" (tailTarget ready heap nonce balance root hash) := by rw [restored,innerEq]
  have frame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with
      globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
      memory:=finalMemory source.memory heap nonce balance root hash,clock:=source.clock-1} := by
    rw [postEq]
    rfl
  have clock := congrArg PanSemStateFiniteExact.clock frame
  change post.clock=source.clock-1 at clock
  have globals := congrArg PanSemStateFiniteExact.globals frame
  change post.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64))) at globals
  have rounded : (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 := by
    rw [PersistentAlloc.rounded_nat heap 56#64 (by change heap.toNat+56+7<2^64; omega)]
    change (heap.toNat+56+7)/8*8=heap.toNat+56
    omega
  refine ⟨positive,room,returnedEq,clock,frame,rounded,?_,?_,?_,?_⟩
  · exact ⟨AccountDecode.Image.of_agreement _ post heap image (by rw [postEq] <;> rfl) (by rw [postEq] <;> rfl) (by rw [postEq] <;> rfl)⟩
  · intro query outside
    rw [postEq]
    exact window query outside
  · intro key different
    rw [globals]
    exact HeapGlobals.update source (PersistentAlloc.rounded heap 56#64) key different
  · rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]

end InitECandidate.Solver.Mpt.AccountNew

#print axioms InitECandidate.Solver.Mpt.AccountNew.body_normal
