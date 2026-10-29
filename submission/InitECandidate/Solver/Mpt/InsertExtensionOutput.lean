import InitECandidate.Solver.Mpt.InsertExtensionPrefixScope
import InitECandidate.Solver.Mpt.TrieWalkRead

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The whole original extension dispatch derives both real field loads,
the actual bounded comparison, descent or split, and both lexical scopes. -/
theorem extension_output_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=2#64)
    (nodeClean : TrieWalk.Uncached source.memory node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source extensionScope=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  let path:=graph.path node member active (Or.inr tag)
  have pointerStored : source.memory (node+32#64)=.word (wordAt source.memory (node+32#64)):=by
    simp only [wordAt,path.pointerStored,MemoryBytes.wordBits]
  have sizeStored : source.memory (node+40#64)=.word (wordAt source.memory (node+40#64)):=by
    simp only [wordAt,path.sizeStored,MemoryBytes.wordBits]
  have pointerRead : eval source (nodeFieldExpression 32#64)=some (.val (.word (wordAt source.memory (node+32#64)))):=by
    simpa only [nodeFieldExpression,TrieWalk.nodeField] using TrieWalk.node_field_read source node 32#64 _ nodeCell path.pointerMapped pointerStored
  rw [extension_shapes.1] at normal
  obtain ⟨first,keyRun,endpoint⟩:=Input.declaration_none_word source target "seg" (nodeFieldExpression 32#64) (wordAt source.memory (node+32#64)) extensionLengthScope pointerRead normal
  let keyed:=QueryBranch.bind source "seg" (wordAt source.memory (node+32#64))
  have keyedNode : keyed.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other source "seg" "node" _ (by decide)).trans nodeCell
  have sizeRead : eval keyed (nodeFieldExpression 40#64)=some (.val (.word (wordAt source.memory (node+40#64)))):=by
    simpa only [nodeFieldExpression,TrieWalk.nodeField] using TrieWalk.node_field_read keyed node 40#64 _ keyedNode path.sizeMapped sizeStored
  rw [extension_shapes.2.1] at keyRun
  obtain ⟨inner,lengthRun,lengthEndpoint⟩:=Input.declaration_none_word keyed first "sl" (nodeFieldExpression 40#64) (wordAt source.memory (node+40#64)) extensionPrefixScope sizeRead keyRun
  let ready:=QueryBranch.bind keyed "sl" (wordAt source.memory (node+40#64))
  have current (name : String) (notSegment : ofString "seg"≠ofString name) (notLength : ofString "sl"≠ofString name) : ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (bind_lookup_other keyed "sl" name _ notLength).trans (bind_lookup_other source "seg" name _ notSegment)
  have segmentCell : ready.locals.lookup (ofString "seg")=some (.val (.word (wordAt source.memory (node+32#64)))):=
    (bind_lookup_other keyed "sl" "seg" _ (by decide)).trans (bind_lookup_same source "seg" _)
  have oldLengthCell : ready.locals.lookup (ofString "sl")=some (.val (.word (wordAt source.memory (node+40#64)))):=bind_lookup_same keyed "sl" _
  have keyedPending:=pending.after_scalar source keyed "seg" (wordAt source.memory (node+32#64)) (by decide) (by decide) (by decide) (by decide) rfl
  have readyPending:=keyedPending.after_scalar keyed ready "sl" (wordAt source.memory (node+40#64)) (by decide) (by decide) (by decide) (by decide) rfl
  obtain ⟨output⟩:=extension_prefix_scope_output ready inner heap node key level length pointer size graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated query readyPending member active tag nodeClean
    ((current _ (by decide) (by decide)).trans nodeCell) ((current _ (by decide) (by decide)).trans keyCell)
    ((current _ (by decide) (by decide)).trans levelCell) ((current _ (by decide) (by decide)).trans lengthCell)
    ((current _ (by decide) (by decide)).trans pointerCell) ((current _ (by decide) (by decide)).trans sizeCell) segmentCell oldLengthCell
    before bounded payload extra floor empty domain installed heapCell frontier aligned lengthRun
  obtain ⟨withLength⟩:=output.restore_scope keyed ready inner graph graph heap key length level limit nodeLower pathLower property "sl" (wordAt source.memory (node+40#64))
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
  rw [endpoint,lengthEndpoint]
  exact withLength.restore_scope source keyed (restore keyed "sl" inner) graph graph heap key length level limit nodeLower pathLower property "seg" (wordAt source.memory (node+32#64))
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.extension_output_normal
