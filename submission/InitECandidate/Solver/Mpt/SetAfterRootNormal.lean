import InitECandidate.Solver.Mpt.SetOutput
import InitECandidate.Solver.Mpt.SetRootProtected
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

theorem mutation_prefix : Input.LocalPrefix (ofString "m") mutationChoice := by
  rw [mutation_shapes.2.2.1,deletion_shape,insertCall]
  apply Input.LocalPrefix.ite
  all_goals exact Input.LocalPrefix.call (some (ofString "root")) _ _ (by intro name equal; cases equal; decide)

/-- The actual mutation and final root store derive a complete setter
suffix result. The header's separation is established before the store
from the genuinely reached mutation output, even when old nodes precede it. -/
theorem after_root_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (heap cursor frame root m key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid root)
    (small : length.toNat≤64) (empty : property 0#64 0#64)
    (owned : pointer≠0#64→size≠0#64→TrieWalk.Payload source.memaddrs pointer size limit ∧ property pointer size)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root)))
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m))) (mapped : source.memaddrs m)
    (headerSafe : graph.ProtectedWord m) (headerAbove : DeleteFrame.ceiling≤m.toNat) (headerBefore : m.toNat<heap.toNat)
    (headerAway : TrieWalk.PathWordAway key length.toNat m)
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterRoot=(some (.returned value),target)) :
    Nonempty (Output source target value m graph heap key length limit nodeLower pathLower property (mutationAllowance pathLower)) := by
  rw [mutation_shapes.2.1] at normal
  obtain ⟨middle,called,returned⟩:=Input.sequence_returned source target mutationChoice footer value
    (fun result=>(mutation_prefix.summary_full source).2.1 result) normal
  obtain ⟨output⟩:=mutation_normal source middle heap cursor frame root key length pointer size graph limit nodeLower pathLower property
    valuesModel regions disjoint paths pathRegions separated query member small empty owned rootCell nkCell pointerCell sizeCell
    heapCell heapArena heapAligned scratch scratchBefore floor pathFloor nodeFloor little installed called
  have currentM : middle.locals.lookup (ofString "m")=some (.val (.word m)):=by
    rw [output.locals]
    simpa [HolFiniteMapExact.update,FUPDATE,ofString] using mCell
  have currentRoot : middle.locals.lookup (ofString "root")=some (.val (.word output.root)):=by
    rw [output.locals]
    simp [HolFiniteMapExact.update,FUPDATE]
  have currentMapped : middle.memaddrs m:=by rw [output.domain]; exact mapped
  have currentHeader := (output.protectedWords m headerSafe headerAbove headerBefore headerAway).2
  obtain ⟨executed,stored,footerFields,next,same,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=
    footer_graph_protected middle m output.root currentM currentRoot currentMapped output.next limit nodeLower pathLower output.heap.toNat property
      output.values output.regions output.disjoint output.paths output.pathRegions output.separated currentHeader
  have comparison:=returned.symm.trans executed
  have answer : value=.val (.word 0#64):=by
    have observed:=congrArg Prod.fst comparison
    simpa using observed
  have endpoint : target=emptyLocalsHOLFinite (rootStored middle m output.root):=congrArg Prod.snd comparison
  rw [endpoint]
  exact ⟨{
    root:=output.root
    heap:=output.heap
    answer:=answer
    rootStored:=stored
    domain:=output.domain
    endian:=output.endian
    code:=output.code
    globalsNonHeap:=output.globalsNonHeap
    price:=output.price
    heapCell:=output.heapCell
    heapArena:=output.heapArena
    heapAligned:=output.heapAligned
    grows:=output.grows
    fields:=output.fields.trans graph output.next footerFields output.members
    next:=next
    members:=by intro node live; rw [same]; exact output.members node live
    freshMembers:=by intro node live; rw [same] at live; exact output.freshMembers node live
    rootMember:=by rw [same]; exact output.rootMember
    regions:=nextRegions
    disjoint:=nextDisjoint
    values:=nextValues
    paths:=nextPaths
    pathRegions:=nextPathRegions
    separated:=nextSeparated
    protectedWords:=by
      intro address safe above before away
      obtain ⟨word,nextSafe⟩:=output.protectedWords address safe above before away
      refine ⟨?_,nextSafe.of_fields output.next next address same footerFields⟩
      intro different
      exact (if_neg different).trans word }⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.mutation_prefix
#print axioms InitECandidate.Solver.Mpt.SetTrie.after_root_normal
