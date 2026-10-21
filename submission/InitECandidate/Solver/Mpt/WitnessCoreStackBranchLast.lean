import InitECandidate.Solver.Mpt.WitnessCoreStackReturnFrame
import InitECandidate.Solver.Mpt.WitnessCoreBranchReturnFrame
import InitECandidate.Solver.Mpt.WitnessCoreBranchLast
import InitECandidate.Solver.Mpt.WitnessCoreResultNode

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine final-child branch pops its real activation and delivers
its owned branch node after the parent's allocation frontier. The real
parser frame and subsequent stores preserve the complete older stack,
including pending hashes, while the actual pop decreases its rank. -/
theorem branch_children_last_stack_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit node child : BitVec 64) (entry : Entry) (rest : List Entry)
    (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val) (last : ¬index.val+1<16)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (payload : entry.data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source branchChildren=(none,post)) :
    View post db cursor.toNat heap.toNat rest ∧ ResultOwned post (max (resultLower rest) entry.data.payload.startAddress) heap.toNat node ∧
      post.locals.lookup (ofString "top")=some (.val (.word (top rest))) ∧
      post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key) ∧ Rlp.Validation.Arena post cursor limit ∧
      (∀ name : String,ofString "i"≠ofString name→ ofString "arr2"≠ofString name→ ofString "bv"≠ofString name→
        ofString "occ"≠ofString name→ ofString "top"≠ofString name→ ofString "result"≠ofString name→
        post.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      (∀ query : BitVec 64,entry.record.toNat+88≤query.toNat→ query.toNat<entry.data.payload.startAddress→ post.memory query=source.memory query) ∧
      post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code ∧
      WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames rest) .returning true<
        WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .returning true := by
  have head:=view.records entry List.mem_cons_self
  have headBefore:=view.before entry List.mem_cons_self
  have headMark:=view.marks entry List.mem_cons_self
  have before:=headBefore.mono entry.data entry.mark heap.toNat headMark
  have headAbove:=view.above entry List.mem_cons_self
  have recordUpper:=head.ceiling
  have heapLower : 2713731432≤heap.toNat:=by have lower:=head.arrayFloor; have upper:=before.1; omega
  have below : cursor.toNat≤2713717616:=by omega
  let ready:=branchCounterEntry source entry.record node child index occupied
  let nextOccupied:=occupiedNext index occupied used child
  let currentData:=(WitnessRecord.BranchCounter.occupied nextOccupied).description entry.data node index occupied
  obtain ⟨item,built,header,bytes,flag,selected,valid,enough,upper,scratch,globals,domain,endian,code,postEq,above⟩:=
    branch_children_last_normal source post entry.record db node (top rest) child heap cursor limit entry.data index occupied used last head payload
      topCell branchCell indexCell resultCell view.links.1 arena before headAbove below heapLower installed normal
  have owned:=head.owned
  simp only [payload,WitnessRecord.Payload.Owned] at owned
  have nodeUpper:=owned.1.upper
  have indexBound:=index.isLt
  have childNumber : (WitnessRecord.childAddress node index).toNat=node.toNat+(32+8*index.val):=
    byteAddress_toNat node (32+8*index.val) (by omega)
  have occupiedNumber : (entry.record+40#64).toNat=entry.record.toNat+40:=byteAddress_toNat entry.record 40 (by omega)
  have memory (query : BitVec 64) (first : entry.record.toNat+88≤query.toNat) (last : query.toNat<entry.data.payload.startAddress) : post.memory query=source.memory query:=by
    have nodeBefore : query.toNat<node.toNat:=by simpa only [payload,WitnessRecord.Payload.startAddress] using last
    rw [postEq,branch_finished_memory ready built node (top rest) currentData header bytes flag nextOccupied owned.1 query nodeBefore]
    have parsed:=above query (by omega)
    exact parsed.trans (branch_counter_entry_memory source entry.record node child index occupied query
      (by intro same; have numeric:=congrArg BitVec.toNat same; rw [childNumber] at numeric; omega)
      (by intro same; have numeric:=congrArg BitVec.toNat same; rw [occupiedNumber] at numeric; omega))
  have tail:=view.return_tail_frame source post db cursor.toNat heap.toNat cursor.toNat heap.toNat entry rest (Nat.le_refl _) (Nat.le_refl _) domain memory
  have readyView:=branch_counter_entry_view source entry.record db node child entry.data index occupied used head payload
  have readyOwned:=readyView.owned
  change AllocatedBytes.Arena node 176 ∧ node.toNat%8=0 ∧ ready.memory node=.word 3#64 at readyOwned
  have nodeFloor : 2713731432≤node.toNat:=by simpa only [payload,WitnessRecord.Payload.startAddress] using head.payloadFloor
  have postTag : post.memory node=.word 3#64:=by
    rw [postEq,branch_finished_tag]
    exact (above node (by omega)).trans readyOwned.2.2
  have parentLower : resultLower rest≤node.toNat:=by simpa only [payload,WitnessRecord.Payload.startAddress] using view.parent_result_lower source db cursor.toNat heap.toNat entry rest
  have nodeBefore : node.toNat+176≤heap.toNat:=by simpa only [payload,WitnessRecord.Payload.endAddress] using before.2
  have fresh : max (resultLower rest) entry.data.payload.startAddress≤node.toNat:=max_le parentLower (by simp only [payload,WitnessRecord.Payload.startAddress]; exact Nat.le_refl _)
  have postOwned : ResultOwned post (max (resultLower rest) entry.data.payload.startAddress) heap.toNat node:=
    Or.inr (ResultNode.of_region post node 3#64 176 _ heap.toNat owned.1 (by decide) owned.2.1 fresh nodeBefore postTag (by decide))
  have fields:=branch_finished_fields ready built node (top rest) currentData header bytes flag nextOccupied
  have actualTop : post.locals.lookup (ofString "top")=some (.val (.word (top rest))):=by rw [postEq]; exact fields.1
  have actualResult : post.locals.lookup (ofString "result")=some (.val (.word node)):=by rw [postEq]; exact fields.2
  have preserved (name : String) (notI : ofString "i"≠ofString name) (notArray : ofString "arr2"≠ofString name)
      (notValue : ofString "bv"≠ofString name) (notOcc : ofString "occ"≠ofString name) (notTop : ofString "top"≠ofString name) (notResult : ofString "result"≠ofString name) :
      post.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    rw [postEq]
    exact (branch_finished_other ready built node (top rest) currentData header bytes flag nextOccupied name notArray notValue notOcc notTop notResult).trans
      (branch_counter_entry_local source entry.record node child index occupied name notI)
  have rank : WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames rest) .returning true<
      WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames (entry::rest)) .returning true:=by
    simpa only [frames,List.map_cons] using WitnessStackRank.pop (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames rest) entry.data.payload.frame
  exact ⟨tail,postOwned,actualTop,actualResult,globals,scratch,preserved,memory,domain,endian,code,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.branch_children_last_stack_normal
