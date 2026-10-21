import InitECandidate.Solver.Rlp.SlicesSnapshotCall

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine enclosing normal return derives the original converter's
actual allocated array snapshot and real caller continuation. This normal
inversion supplies data even when the entire execution has small cost. -/
theorem scoped_snapshot_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_list_to_slices") arguments continuation)=(some (.returned value),post)) :
    1≤source.clock ∧ ∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,∃ items : List ListItem,∃ count : BitVec 64,∃ inner,
      Snapshot (Input.LocalEffects.erase source) target pointer length heap cursor limit count items ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (result heap count)) continuation=(some (.returned value),inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code installed)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post name resultShape (ofString "rlp_list_to_slices") arguments _ body continuation callee resultShape args called value normal
  have entryArena:=Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  obtain ⟨items,count,valueEq,snapshot⟩:=body_snapshot (callEntryStateHOLFinite source callee) target pointer length heap cursor limit cutoff pointerLocal lengthLocal entryArena
    heapGlobal heapBound heapAligned before sizeBound aligned scratchBelow inputAbove installed answer bodyRun
  rw [valueEq] at continued
  exact ⟨funded,target,items,count,inner,snapshot,continued,endpoint⟩

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.scoped_snapshot_normal
