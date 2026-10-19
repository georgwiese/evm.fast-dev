import InitECandidate.Solver.Mpt.AccountDecodeCursors
import InitECandidate.Solver.Mpt.AccountDecodeCall
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual normal ignored decoder calls retain the caller's arena and
derive the bounded64-byte allocation, including real callee/ABI execution. -/
theorem ignored_cursors (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out : BitVec 64) (cutoff : Nat)
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length out))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "decode_account_from_leaf") arguments)=(none,post)) :
    1≤source.clock ∧ Rlp.Validation.Arena post cursor limit ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      heap.toNat+64≤33806089496 ∧ (PersistentAlloc.rounded heap 64#64).toNat≤33806089496 := by
  obtain ⟨positive,actualValues,actualBody,actualCallee,shape,target,returned,actualArgs,called,bodyRun,checked,postEq,fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "decode_account_from_leaf") arguments normal
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  obtain ⟨callee,expected,p,n,a⟩ := environment source.code.lookup pointer length out (original_code source.code installed)
  rw [expected] at called
  simp only [Option.some.injEq,Prod.mk.injEq] at called
  rcases called with ⟨rfl,rfl,rfl⟩
  obtain ⟨nextArena,nextHeap,room,bounded⟩ := body_cursors (callEntryStateHOLFinite source callee) target pointer length heap cursor limit out cutoff p n a
    (Rlp.Validation.Arena.of_fields source _ cursor limit arena rfl rfl) heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove output installed returned bodyRun
  refine ⟨positive,?_,?_,room,bounded⟩
  · rw [postEq]
    exact Rlp.Validation.Arena.of_fields target _ cursor limit nextArena rfl rfl
  · rw [postEq]
    exact nextHeap

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.ignored_cursors
