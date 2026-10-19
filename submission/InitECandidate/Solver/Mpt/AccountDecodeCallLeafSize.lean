import InitECandidate.Solver.Mpt.AccountDecodeLeafSize
import InitECandidate.Solver.Mpt.AccountDecodeCall
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- A genuine successful ignored original decoder call derives its actual
149-byte leaf bound and fixed source price, including the real call tick. -/
theorem ignored_leaf_size (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out emptyRoot emptyHash : BitVec 64) (cutoff : Nat)
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length out))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "decode_account_from_leaf") arguments)=(none,post)) :
    length.toNat≤149 ∧ source.clock-post.clock≤28752 := by
  obtain ⟨positive,actualValues,actualBody,actualCallee,shape,target,returned,actualArgs,called,bodyRun,checked,postEq,fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "decode_account_from_leaf") arguments normal
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  obtain ⟨callee,expected,p,n,a⟩ := environment source.code.lookup pointer length out (original_code source.code installed)
  rw [expected] at called
  simp only [Option.some.injEq,Prod.mk.injEq] at called
  rcases called with ⟨rfl,rfl,rfl⟩
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨small,price⟩ := body_leaf_size entry target pointer length heap cursor limit out emptyRoot emptyHash cutoff p n a
    (Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl) heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove
    rootGlobal hashGlobal output installed returned bodyRun
  have clock := evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at clock
  change target.clock≤source.clock-1 at clock
  change source.clock-1-target.clock≤28751 at price
  rw [postEq]
  exact ⟨small,by change source.clock-target.clock≤28752; omega⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.ignored_leaf_size
