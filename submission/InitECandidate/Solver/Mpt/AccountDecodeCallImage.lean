import InitECandidate.Solver.Mpt.AccountDecodeNormal
import InitECandidate.Solver.Mpt.AccountDecodeCall
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The actual ignored account decoder call produces a physical account
image and its real allocation, memory footprint and paid call cost.
Current empty references are owned input globals, not future results. -/
theorem ignored_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out emptyRoot emptyHash : BitVec 64) (cutoff : Nat)
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length out))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "decode_account_from_leaf") arguments)=(none,post)) :
    1≤source.clock ∧ Nonempty (Image post out) ∧ Rlp.Validation.Arena post cursor limit ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      heap.toNat+64≤33806089496 ∧ HeapGlobals source post ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat →
        query.toNat<out.toNat ∨ out.toNat+56≤query.toNat → post.memory query=source.memory query) ∧
      source.clock-post.clock≤191*length.toNat+293 := by
  obtain ⟨positive,actualValues,actualBody,actualCallee,shape,target,returned,actualArgs,called,bodyRun,checked,postEq,fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "decode_account_from_leaf") arguments normal
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  obtain ⟨callee,expected,p,n,a⟩ := environment source.code.lookup pointer length out (original_code source.code installed)
  rw [expected] at called
  simp only [Option.some.injEq,Prod.mk.injEq] at called
  rcases called with ⟨rfl,rfl,rfl⟩
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨result,⟨image⟩,nextArena,nextHeap,room,window,price⟩ := body_normal entry target pointer length heap cursor limit out emptyRoot emptyHash cutoff p n a
    (Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl) heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove
    rootGlobal hashGlobal rootArena hashArena output installed returned bodyRun
  have nonheap : HeapGlobals source target := by
    intro key notHeap
    by_cases scratch : key=ofString "scratch_ptr"
    · subst key
      exact nextArena.cursorGlobal.trans arena.cursorGlobal.symm
    · have preserved := globals key source.code installed notHeap scratch entry rfl
      rw [bodyRun] at preserved
      exact congrArg Prod.snd preserved
  have clock := evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at clock
  change target.clock≤source.clock-1 at clock
  change source.clock-1-target.clock≤191*length.toNat+292 at price
  rw [postEq]
  exact ⟨positive,⟨Image.of_agreement target _ out image rfl (by rfl) (by rfl)⟩,
    Rlp.Validation.Arena.of_fields target _ cursor limit nextArena rfl rfl,nextHeap,room,nonheap,window,
    by change source.clock-target.clock≤_; omega⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.ignored_image
