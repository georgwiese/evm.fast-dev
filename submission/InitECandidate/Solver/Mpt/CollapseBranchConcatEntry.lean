import InitECandidate.Solver.Mpt.CollapseBranchSuffixProgram
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments
import InitECandidate.Solver.Mpt.NibblesConcatScopedPaths

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem concat_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (nibble child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid child) (active : child≠0#64)
    (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (nibbleCell : source.locals.lookup (ofString "nib")=some (.val (.word nibble)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) concatArguments=
      some (NibblesConcat.callValues nibble 1#64 (wordAt source.memory (child+32#64)) (wordAt source.memory (child+40#64))) := by
  classical
  let path:=graph.path child member active tag
  have pointerStored : source.memory (child+32#64)=.word (wordAt source.memory (child+32#64)):=by simp only [wordAt,path.pointerStored,MemoryBytes.wordBits]
  have lengthStored : source.memory (child+40#64)=.word (wordAt source.memory (child+40#64)):=by simp only [wordAt,path.sizeStored,MemoryBytes.wordBits]
  have pointerRead : eval source (field "child" 32#64)=some (.val (.word (wordAt source.memory (child+32#64)))):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read source "child" child 32#64 _ childCell path.pointerMapped pointerStored
  have lengthRead : eval source (field "child" 40#64)=some (.val (.word (wordAt source.memory (child+40#64)))):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read source "child" child 40#64 _ childCell path.sizeMapped lengthStored
  have nibbleRead : eval source (localVar "nib")=some (.val (.word nibble)):=by simp [eval,localVar,evalHOLExact,toExact,nibbleCell]
  have oneRead : evalHOLExact source.toExact (.const 1#64)=some (.val (.word 1#64)):=rfl
  simp only [eval] at pointerRead lengthRead nibbleRead
  simp only [concatArguments,NibblesConcat.callValues,evalListHOLFinite,evalListHOLExact,nibbleRead,oneRead,pointerRead,lengthRead]

/-- The actual selected nibble and full stored child path are the true
four concatenation arguments. Normal execution derives the fresh joined
buffer, old-word frame and original afterConcat continuation. -/
theorem concat_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nibble child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat nibble 1) (floor : 2701131776≤pathLower)
    (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (nibbleCell : source.locals.lookup (ofString "nib")=some (.val (.word nibble)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source concatScope=(some (.returned value),post)) :
    let childLength:=wordAt source.memory (child+40#64)
    let nextHeap:=PersistentAlloc.rounded heap (1#64+childLength)
    ∃ ready inner,ready.locals=source.locals.update (ofString "cat",.val (.word heap)) ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧ source.clock-ready.clock≤childLength.toNat/8+19 ∧
      evaluateHOLFiniteState ready afterConcat=(some (.returned value),inner) ∧ post=restore source "cat" inner ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧ AllocatedBytes.Arena nextHeap 0 ∧ nextHeap.toNat%8=0 ∧ heap.toNat+1+childLength.toNat≤nextHeap.toNat ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query) ∧
      ∃ next : TrieWalk.Graph ready.memory ready.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower nextHeap.toNat ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes ready.be ∧ next.PathRegions pathLower nextHeap.toNat ∧ next.PathSeparated ∧
        next.PathBuffer ready.be pathLower nextHeap.toNat heap (1+childLength.toNat) := by
  have right:=TrieWalk.Graph.PathBuffer.stored graph source.be pathLower heap.toNat paths pathRegions separated child member active tag
  have args:=concat_arguments source nibble child graph member active tag nibbleCell childCell
  rw [merge_shapes.2.2.1] at normal
  simpa only [show (1#64).toNat=1 from rfl,show (1/8 : Nat)=0 from rfl,Nat.zero_add] using NibblesConcat.scoped_normal_paths source post heap nibble 1#64 (wordAt source.memory (child+32#64)) (wordAt source.memory (child+40#64))
    graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated buffer right floor heapCell frontier aligned little domain installed
      "cat" concatArguments afterConcat args value normal

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.concat_arguments
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.concat_entry
