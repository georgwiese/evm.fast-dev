import InitECandidate.Solver.Mpt.StateInitPathOutputFrame
import InitECandidate.Solver.Mpt.StateInitBoundaryNormal

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessCore

theorem PathOutput.with_locals (input : Guest.InputBlob) (origin post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes : BitVec 64) (output : PathOutput input origin post workspace nodes rootHash codes)
    (locals : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS (ValueHOL 64)) :
    PathOutput input origin {post with locals:=locals} workspace nodes rootHash codes:=
  output.of_erase input origin post {post with locals:=locals} workspace nodes rootHash codes rfl

/-- Actual boundary/heap-floor facts supply every original322 argument and
allocation-frontier premise. The normal return derives the initialized
closed graph, all eight tables and complete empty journal. -/
theorem path_normal_of_boundary (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootHash : BitVec 64) (boundary : StateInitBoundary input source)
    (installed : Input.OriginalCode.Installed source.code) (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word rootHash)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (heapFloor : ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ 2713731432≤heap.toNat)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ workspace nodes codes,PathOutput input source post workspace nodes rootHash codes ∧
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word workspace)):=by
  have saved:=boundary
  obtain ⟨array,nodes,codes,heap,nodeData,codeData,nodeCell,codeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩:=boundary
  obtain ⟨floorHeap,floorCell,floorLower⟩:=heapFloor
  have same : heap=floorHeap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (heapCell.symm.trans floorCell)))
  have lower : 2713731432≤heap.toNat:=by rw [same]; exact floorLower
  obtain ⟨zero,output⟩:=path_body_normal input source post heap nodes rootHash codes saved installed scalars heapCell lower nodeCell rootCell codeCell scratch value normal
  exact ⟨zero,heap,nodes,codes,output,heapCell⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.PathOutput.with_locals
#print axioms InitECandidate.Solver.Mpt.StateInit.path_normal_of_boundary
