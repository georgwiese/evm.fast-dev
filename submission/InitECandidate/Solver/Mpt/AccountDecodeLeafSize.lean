import InitECandidate.Solver.Mpt.AccountDecodeNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- A successful original account decode has at most149 input bytes: four
actual string payloads of at most8,32,32,32 bytes, their real headers of at
most9 each, and the original outer header of at most9. This follows from
the actual two-pass encodings and passed output guards, not an input cap. -/
theorem body_leaf_size (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out emptyRoot emptyHash : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    length.toNat≤149 ∧ source.clock-post.clock≤28751 := by
  obtain ⟨header,payload,a,b,c,d,ready,inner,extent,head,recordRoom,⟨results⟩,view,heapEntry,domain,endian,codeEq,prefixMemory,tailRun,frame⟩ :=
    body_fields source post pointer length heap cursor limit out cutoff pointerCell lengthCell outputCell arena heapGlobal heapBound before sizeBound
      aligned scratchBelow inputAbove output installed returned normal
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [codeEq]; exact installed
  have rootEq := reached_tail_global source ready post inner (ofString "empty_trie_root") installed codeEq (by decide) (by decide) _ normal tailRun frame
  have hashEq := reached_tail_global source ready post inner (ofString "empty_code_hash") installed codeEq (by decide) (by decide) _ normal tailRun frame
  have cell0 := results.cell0
  have cell1 := results.cell1
  have cell2 := results.cell2
  have cell3 := results.cell3
  rw [results.exact0] at cell0
  rw [results.exact1] at cell1
  rw [results.exact2] at cell2
  rw [results.exact3] at cell3
  obtain ⟨result,stringFlags,nonceBound,balanceBound,rootWidth,hashWidth,window,rootStored,hashStored⟩ :=
    after_fields_normal ready inner out (Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 0) a.header a.payload a.flag
      (Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 1) b.header b.payload b.flag
      (Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 2) c.header c.payload c.flag
      (Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 3) d.header d.payload d.flag emptyRoot emptyHash
      view.outputCell cell0 cell1 cell2 cell3 (rootEq.trans rootGlobal) (hashEq.trans hashGlobal) output view.arena.domain readyInstalled returned tailRun
  have selectedHeader (index : Nat) (item : Rlp.ListItem) (selected : [a,b,c,d][index]?=some item) : item.header.toNat≤9 := by
    obtain ⟨offset,path,inside,valid,encoded⟩ := Rlp.ListItems.at ready (pointer+header) payload.toNat [a,b,c,d] view.itemsModel index item selected
    exact (Rlp.Header.Valid.result_fields item.size item.header item.payload item.flag valid).1
  have head0 := selectedHeader 0 a rfl
  have head1 := selectedHeader 1 b rfl
  have head2 := selectedHeader 2 c rfl
  have head3 := selectedHeader 3 d rfl
  have rootBound : c.payload.toNat≤32 := by rcases rootWidth with width | width <;> rw [width] <;> decide
  have hashBound : d.payload.toNat≤32 := by rcases hashWidth with width | width <;> rw [width] <;> decide
  have total := Rlp.ListItems.total_size ready (pointer+header) payload.toNat [a,b,c,d] view.itemsModel
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Rlp.ListItem.size] at total
  have small : length.toNat≤149 := by omega
  have price := body_cost source pointer length heap cursor limit out cutoff pointerCell lengthCell outputCell arena heapGlobal heapBound before sizeBound
    aligned scratchBelow inputAbove output installed
  rw [normal] at price
  change source.clock-post.clock≤191*length.toNat+292 at price
  exact ⟨small,by omega⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.body_leaf_size
