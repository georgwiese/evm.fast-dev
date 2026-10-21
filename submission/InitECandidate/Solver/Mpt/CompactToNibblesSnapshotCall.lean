import InitECandidate.Solver.Mpt.CompactToNibblesSnapshot
import InitECandidate.Solver.Mpt.CompactToNibblesCost
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ScopedCallTrace
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

private theorem caller_origin (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (length : Nat) (heap cursor limit : BitVec 64) (nibbles : Nat) (leaf : BitVec 64)
    (snapshot : Snapshot (callEntryStateHOLFinite source callee) target length heap cursor limit nibbles leaf) :
    Snapshot source target length heap cursor limit nibbles leaf :=
  ⟨snapshot.positive,snapshot.outputArena,snapshot.nibbleBound,snapshot.leafBinary,snapshot.arena,snapshot.heapCell,
    snapshot.nextArena,snapshot.nextAligned,snapshot.grows,snapshot.metadata,snapshot.memory⟩

/-- Actual original compact conversion either stops within its local
allowance or supplies the real fresh output, heap, scratch and memory frame
at its genuine returned continuation. -/
theorem scoped_snapshot_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap cursor limit : BitVec 64) (length : Nat) (bounded : length≤1024)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))])
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "compact_to_nibbles") arguments continuation)=(outcome,post)) :
    source.clock-post.clock≤length/4+7 ∨ ∃ target nibbles leaf inner,
      Snapshot source target length heap cursor limit nibbles leaf ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤length/4+7 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (output heap nibbles leaf)) continuation=(outcome,inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Input.word_pair_environment source.code.lookup (ofString "compact_to_nibbles")
    (ofString "p") (ofString "n") body resultShape pointer (BitVec.ofNat 64 length) (by decide) (original_code source.code installed)
  have entryArena:=Rlp.Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have price:=body_cost (callEntryStateHOLFinite source callee) pointer length (by omega) pointerLocal lengthLocal installed
  rcases Input.CallNormal.scoped_trace source post name resultShape (ofString "compact_to_nibbles") arguments _ body continuation callee resultShape (length/4+6)
      args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,spent,continued,endpoint⟩:=reached
    obtain ⟨nibbles,leaf,valueEq,snapshot⟩:=body_snapshot (callEntryStateHOLFinite source callee) target pointer heap cursor limit length bounded
      pointerLocal lengthLocal heapCell heapArena aligned entryArena installed value bodyRun
    rw [valueEq] at continued
    exact Or.inr ⟨target,nibbles,leaf,inner,caller_origin source target callee length heap cursor limit nibbles leaf snapshot,forward,spent,continued,endpoint⟩

/-- Price only genuine continuations reached from the real original
compact return, after deriving every output/heap/frame fact from that run. -/
theorem scoped_snapshot_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap cursor limit : BitVec 64) (length : Nat) (bounded : length≤1024)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))])
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (tail : ∀ target nibbles leaf,Snapshot source target length heap cursor limit nibbles leaf→
      let ready:=Input.CallNormal.continuationEntry source target name (output heap nibbles leaf)
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "compact_to_nibbles") arguments continuation)).2.clock≤length/4+7+tailPrice := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Input.word_pair_environment source.code.lookup (ofString "compact_to_nibbles")
    (ofString "p") (ofString "n") body resultShape pointer (BitVec.ofNat 64 length) (by decide) (original_code source.code installed)
  have entryArena:=Rlp.Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have price:=body_cost (callEntryStateHOLFinite source callee) pointer length (by omega) pointerLocal lengthLocal installed
  have total:=Input.ClockCost.scoped_reached_current source name resultShape (ofString "compact_to_nibbles") arguments _ body continuation callee resultShape
    (length/4+6) tailPrice args called price (by
      intro target value bodyRun checked
      obtain ⟨nibbles,leaf,valueEq,snapshot⟩:=body_snapshot (callEntryStateHOLFinite source callee) target pointer heap cursor limit length bounded
        pointerLocal lengthLocal heapCell heapArena aligned entryArena installed value bodyRun
      rw [valueEq]
      exact tail target nibbles leaf (caller_origin source target callee length heap cursor limit nibbles leaf snapshot))
  exact total.trans (by omega)

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.scoped_snapshot_trace
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.scoped_snapshot_cost
