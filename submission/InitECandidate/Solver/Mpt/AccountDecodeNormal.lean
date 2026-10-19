import InitECandidate.Solver.Mpt.AccountDecodeFieldsNormal
import InitECandidate.Solver.Mpt.AccountAfterFieldsNormal
import InitECandidate.Solver.Mpt.AccountDecodeGlobals
import InitECandidate.Solver.Mpt.AccountDecodeCursors
import InitECandidate.Solver.Mpt.AccountDecodeCost
import InitECandidate.Solver.Mpt.AccountImage

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 10000 in
/-- Complete actual normal original account decoder: scalar0 return, real
physical account/reference image, restored arena, bounded64-byte record
allocation, ordinary-memory footprint and observed source cost. All entry
facts are current ownership/environment facts, not future helper models. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ Nonempty (Image post out) ∧ Rlp.Validation.Arena post cursor limit ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))) ∧ heap.toNat+64≤33806089496 ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat →
        query.toNat<out.toNat ∨ out.toNat+56≤query.toNat → post.memory query=source.memory query) ∧
      source.clock-post.clock≤191*length.toNat+292 := by
  obtain ⟨header,payload,a,b,c,d,ready,inner,extent,recordRoom,⟨results⟩,view,heapEntry,domain,endian,codeEq,prefixMemory,tailRun,frame⟩ :=
    body_fields source post pointer length heap cursor limit out cutoff pointerCell lengthCell outputCell arena heapGlobal heapBound before sizeBound
      aligned scratchBelow inputAbove output installed returned normal
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [codeEq]; exact installed
  have rootEq := reached_tail_global source ready post inner (ofString "empty_trie_root") installed codeEq (by decide) (by decide) _ normal tailRun frame
  have hashEq := reached_tail_global source ready post inner (ofString "empty_code_hash") installed codeEq (by decide) (by decide) _ normal tailRun frame
  obtain ⟨h0,p0,f0,value0,head0,positive0,bound0,binary0,list0⟩ := results.valid0
  obtain ⟨h1,p1,f1,value1,head1,positive1,bound1,binary1,list1⟩ := results.valid1
  obtain ⟨h2,p2,f2,value2,head2,positive2,bound2,binary2,list2⟩ := results.valid2
  obtain ⟨h3,p3,f3,value3,head3,positive3,bound3,binary3,list3⟩ := results.valid3
  have cell0 := results.cell0
  have cell1 := results.cell1
  have cell2 := results.cell2
  have cell3 := results.cell3
  rw [value0] at cell0
  rw [value1] at cell1
  rw [value2] at cell2
  rw [value3] at cell3
  let base0 := Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 0
  let base1 := Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 1
  let base2 := Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 2
  let base3 := Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 3
  obtain ⟨result,stringFlags,nonceBound,balanceBound,rootWidth,hashWidth,window,rootStored,hashStored⟩ :=
    after_fields_normal ready inner out base0 h0 p0 f0 base1 h1 p1 f1 base2 h2 p2 f2 base3 h3 p3 f3 emptyRoot emptyHash
      view.outputCell cell0 cell1 cell2 cell3 (rootEq.trans rootGlobal) (hashEq.trans hashGlobal) output view.arena.domain readyInstalled returned tailRun
  have selectedRootArena := view.payload_arena ready heap (pointer+header) payload cursor limit out cutoff [a,b,c,d] (by omega) 2 c rfl h2 p2 bound2
  have selectedHashArena := view.payload_arena ready heap (pointer+header) payload cursor limit out cutoff [a,b,c,d] (by omega) 3 d rfl h3 p3 bound3
  have rootRegion : AllocatedBytes.Arena (if p2=0#64 then emptyRoot else base2+h2) 32 := by
    by_cases zero : p2=0#64
    · simpa only [if_pos zero] using rootArena
    · have width := rootWidth.resolve_left zero
      rw [if_neg zero]
      simpa [width, base2] using selectedRootArena
  have hashRegion : AllocatedBytes.Arena (if p3=0#64 then emptyHash else base3+h3) 32 := by
    by_cases zero : p3=0#64
    · simpa only [if_pos zero] using hashArena
    · have width := hashWidth.resolve_left zero
      rw [if_neg zero]
      simpa [width, base3] using selectedHashArena
  have finalMemory := congrArg PanSemStateFiniteExact.memory frame
  change post.memory=inner.memory at finalMemory
  have finalDomain := (Input.evaluation_fields source post body (some (.returned returned)) normal).1.trans arena.domain
  have image : Image post out := ⟨output,finalDomain,_,_,by rw [finalMemory]; exact rootStored,by rw [finalMemory]; exact hashStored,rootRegion,hashRegion⟩
  obtain ⟨nextArena,nextHeap,room,boundedHeap⟩ := body_cursors source post pointer length heap cursor limit out cutoff pointerCell lengthCell outputCell arena heapGlobal heapBound before sizeBound
    aligned scratchBelow inputAbove output installed returned normal
  have price := body_cost source pointer length heap cursor limit out cutoff pointerCell lengthCell outputCell arena heapGlobal heapBound before sizeBound
    aligned scratchBelow inputAbove output installed
  rw [normal] at price
  refine ⟨result,⟨image⟩,nextArena,nextHeap,room,?_,price⟩
  intro query beyond outsideRecords outsideOutput
  rw [finalMemory]
  exact (window query outsideOutput).trans (prefixMemory query beyond outsideRecords)

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.body_normal
