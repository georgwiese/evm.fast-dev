import InitECandidate.Solver.Rlp.SlicesSnapshot
import InitECandidate.Solver.Input.ScopedCallTrace
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Every actual original list-conversion scope stops within its body/call
allowance or exposes the real allocated-array snapshot at its genuine saved
caller continuation. No future normal conversion is assumed. -/
theorem scoped_snapshot_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_list_to_slices") arguments continuation)=(outcome,post)) :
    source.clock-post.clock≤71*length.toNat+35 ∨ ∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,∃ items : List ListItem,∃ count : BitVec 64,∃ inner,
      Snapshot (Input.LocalEffects.erase source) target pointer length heap cursor limit count items ∧
      1≤source.clock ∧ target.clock≤source.clock ∧ source.clock-target.clock≤71*length.toNat+35 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (result heap count)) continuation=(outcome,inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code installed)
  have entryArena:=Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have fits : pointer.toNat+length.toNat<2^64:=by have upper:=heap.isLt; omega
  have price:=body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed
  rcases Input.CallNormal.scoped_trace source post name resultShape (ofString "rlp_list_to_slices") arguments _ body continuation callee resultShape
      (71*length.toNat+34) args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,spent,continued,endpoint⟩:=reached
    obtain ⟨items,count,valueEq,snapshot⟩:=body_snapshot (callEntryStateHOLFinite source callee) target pointer length heap cursor limit cutoff pointerLocal lengthLocal entryArena
      heapGlobal heapBound heapAligned before sizeBound aligned scratchBelow inputAbove installed value bodyRun
    rw [valueEq] at continued
    exact Or.inr ⟨target,items,count,inner,snapshot,funded,forward,spent,continued,endpoint⟩

/-- Price only continuations reached from a genuine original array return.
The current physical snapshot is derived before the continuation obligation. -/
theorem scoped_snapshot_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (tail : ∀ target : PanSemStateFiniteExact 64 Guest.HostMemory,∀ items : List ListItem,∀ count : BitVec 64,
      Snapshot (Input.LocalEffects.erase source) target pointer length heap cursor limit count items→
      let ready:=Input.CallNormal.continuationEntry source target name (result heap count)
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_list_to_slices") arguments continuation)).2.clock≤71*length.toNat+35+tailPrice := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code installed)
  have entryArena:=Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have fits : pointer.toNat+length.toNat<2^64:=by have upper:=heap.isLt; omega
  have price:=body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed
  have total:=Input.ClockCost.scoped_reached_current source name resultShape (ofString "rlp_list_to_slices") arguments _ body continuation callee resultShape
    (71*length.toNat+34) tailPrice args called price (by
      intro target value bodyRun checked
      obtain ⟨items,count,valueEq,snapshot⟩:=body_snapshot (callEntryStateHOLFinite source callee) target pointer length heap cursor limit cutoff pointerLocal lengthLocal entryArena
        heapGlobal heapBound heapAligned before sizeBound aligned scratchBelow inputAbove installed value bodyRun
      rw [valueEq]
      exact tail target items count snapshot)
  exact total.trans (by omega)

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.scoped_snapshot_trace
#print axioms InitECandidate.Solver.Rlp.Slices.scoped_snapshot_cost
