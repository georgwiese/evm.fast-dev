import InitECandidate.Solver.Mpt.DeleteExtensionEntry
import InitECandidate.Solver.Mpt.NibblesConcatScopedPaths

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem concat_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child segment length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid child) (active : child≠0#64)
    (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (lengthCell : source.locals.lookup (ofString "sl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) concatArguments=
      some (NibblesConcat.callValues segment length (wordAt source.memory (child+32#64)) (wordAt source.memory (child+40#64))) := by
  classical
  let path:=graph.path child member active tag
  have pointerStored : source.memory (child+32#64)=.word (wordAt source.memory (child+32#64)):=by simp only [wordAt,path.pointerStored,MemoryBytes.wordBits]
  have lengthStored : source.memory (child+40#64)=.word (wordAt source.memory (child+40#64)):=by simp only [wordAt,path.sizeStored,MemoryBytes.wordBits]
  have pointerRead : evalHOLExact source.toExact (field "nc" 32#64)=some (.val (.word (wordAt source.memory (child+32#64)))):=by
    simp [field,localVar,evalHOLExact,evalListHOLExact,toExact,childCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,path.pointerMapped,pointerStored]
  have lengthRead : evalHOLExact source.toExact (field "nc" 40#64)=some (.val (.word (wordAt source.memory (child+40#64)))):=by
    simp [field,localVar,evalHOLExact,evalListHOLExact,toExact,childCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,path.sizeMapped,lengthStored]
  have segmentRead : evalHOLExact source.toExact (localVar "seg")=some (.val (.word segment)):=by simp [localVar,evalHOLExact,toExact,segmentCell]
  have sizeRead : evalHOLExact source.toExact (localVar "sl")=some (.val (.word length)):=by simp [localVar,evalHOLExact,toExact,lengthCell]
  simp only [concatArguments,NibblesConcat.callValues,evalListHOLFinite,evalListHOLExact,segmentRead,sizeRead,pointerRead,lengthRead]

/-- The original merge's actual cat scope receives the genuinely copied
joined path. Every old node and path is retained at the real rounded heap. -/
theorem concat_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap child segment length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (segmentBuffer : graph.PathBuffer source.be pathLower heap.toNat segment length.toNat) (floor : 2701131776≤pathLower)
    (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (lengthCell : source.locals.lookup (ofString "sl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source concatScope=(some (.returned value),post)) :
    let childLength:=wordAt source.memory (child+40#64)
    let nextHeap:=PersistentAlloc.rounded heap (length+childLength)
    ∃ ready inner,ready.locals=source.locals.update (ofString "cat",.val (.word heap)) ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      source.clock-ready.clock≤length.toNat/8+childLength.toNat/8+19 ∧
      evaluateHOLFiniteState ready lengthScope=(some (.returned value),inner) ∧ post=restore source "cat" inner ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧ AllocatedBytes.Arena nextHeap 0 ∧ nextHeap.toNat%8=0 ∧
      heap.toNat+length.toNat+childLength.toNat≤nextHeap.toNat ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query) ∧
      ∃ next : TrieWalk.Graph ready.memory ready.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower nextHeap.toNat ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes ready.be ∧ next.PathRegions pathLower nextHeap.toNat ∧ next.PathSeparated ∧
        next.PathBuffer ready.be pathLower nextHeap.toNat heap (length.toNat+childLength.toNat) := by
  have right:=TrieWalk.Graph.PathBuffer.stored graph source.be pathLower heap.toNat paths pathRegions separated child member active tag
  have args:=concat_arguments source child segment length graph member active tag segmentCell lengthCell childCell
  rw [merge_shapes.2.2.1] at normal
  exact NibblesConcat.scoped_normal_paths source post heap segment length (wordAt source.memory (child+32#64)) (wordAt source.memory (child+40#64))
    graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated segmentBuffer right floor heapCell frontier aligned little domain installed
      "cat" concatArguments lengthScope args value normal

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.concat_arguments
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.concat_entry
