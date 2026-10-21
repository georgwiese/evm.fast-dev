import InitECandidate.Solver.Mpt.CompactToNibblesSnapshotCall

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine whole scoped return derives the actual compact output and
resumed continuation, independently of any stopping-cost alternative. -/
theorem scoped_snapshot_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap cursor limit : BitVec 64) (length : Nat) (bounded : length≤1024)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))])
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "compact_to_nibbles") arguments continuation)=(some (.returned value),post)) :
    1≤source.clock ∧ ∃ target nibbles leaf inner,
      Snapshot source target length heap cursor limit nibbles leaf ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (output heap nibbles leaf)) continuation=(some (.returned value),inner) ∧
      post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Input.word_pair_environment source.code.lookup (ofString "compact_to_nibbles")
    (ofString "p") (ofString "n") body resultShape pointer (BitVec.ofNat 64 length) (by decide) (original_code source.code installed)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post name resultShape (ofString "compact_to_nibbles") arguments _ body continuation callee resultShape args called value normal
  have entryArena:=Rlp.Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  obtain ⟨nibbles,leaf,valueEq,snapshot⟩:=body_snapshot (callEntryStateHOLFinite source callee) target pointer heap cursor limit length bounded
    pointerLocal lengthLocal heapCell heapArena aligned entryArena installed answer bodyRun
  rw [valueEq] at continued
  exact ⟨funded,target,nibbles,leaf,inner,snapshot.from_call_entry source target callee length heap cursor limit nibbles leaf,continued,endpoint⟩

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.scoped_snapshot_normal
