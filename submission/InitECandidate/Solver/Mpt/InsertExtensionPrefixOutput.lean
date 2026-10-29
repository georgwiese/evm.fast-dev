import InitECandidate.Solver.Mpt.InsertExtensionDescend
import InitECandidate.Solver.Mpt.InsertExtensionSplitNormal
import InitECandidate.Solver.Mpt.InsertNodeOutputTerminal
import InitECandidate.Solver.Mpt.InsertNodeOutputDescend
import InitECandidate.Solver.Mpt.InsertPending

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual extension prefix choice either consumes its positive path
or finishes through the real split and optional extension constructors. -/
theorem extension_prefix_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length prefixLength pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=2#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word (wordAt source.memory (node+32#64)))))
    (oldLengthCell : source.locals.lookup (ofString "sl")=some (.val (.word (wordAt source.memory (node+40#64)))))
    (prefixBound : prefixLength.toNat≤min (wordAt source.memory (node+40#64)).toNat (length.toNat-level.toNat))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source extensionPrefixChoice=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  have oldBound : prefixLength.toNat≤(wordAt source.memory (node+40#64)).toNat:=prefixBound.trans (Nat.min_le_left _ _)
  have queryBound : prefixLength.toNat≤length.toNat-level.toNat:=prefixBound.trans (Nat.min_le_right _ _)
  by_cases matched : prefixLength=wordAt source.memory (node+40#64)
  · have selected : evaluateHOLFiniteState source extensionPrefixChoice=evaluateHOLFiniteState source extensionDescend:=by
      rw [extension_shapes.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,prefixCell,oldLengthCell,matched,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    obtain ⟨child,childMember,slot,addition,nextBound,positive,endpoint⟩:=extension_descend_normal source target node level length prefixLength graph member active tag paths matched
      nodeCell prefixCell levelCell (by omega) bounded (selected.symm.trans normal)
    exact descend_output source target heap key length level node child (node+48#64) (level+prefixLength)
      graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member childMember slot positive nextBound heapCell frontier aligned endpoint
  · have strict : prefixLength.toNat<(wordAt source.memory (node+40#64)).toNat:=by
      have different : prefixLength.toNat≠(wordAt source.memory (node+40#64)).toNat:=by intro same; exact matched (BitVec.toNat_inj.mp same)
      omega
    have selected : evaluateHOLFiniteState source extensionPrefixChoice=evaluateHOLFiniteState source extensionSplitScope:=by
      rw [extension_shapes.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,prefixCell,oldLengthCell,matched,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    obtain ⟨root,localsEq,domainEq,endianEq,codeEq,price,memory,tags,finalHeap,finalHeapCell,finalArena,finalAligned,grows,next,members,rootMember,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated,provenance,protection,_rootClean⟩:=
      extension_split_normal source target heap node key level length prefixLength pointer size graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query
        member active tag nodeCell keyCell levelCell lengthCell pointerCell sizeCell prefixCell segmentCell before strict queryBound payload extra floor empty domain heapCell frontier aligned installed (selected.symm.trans normal)
    exact terminal_output source target heap key length level root finalHeap graph limit nodeLower pathLower property pending.node pending.slot pending.level pending.go localsEq
      domainEq endianEq codeEq finalHeapCell finalArena finalAligned grows (fun address before=>memory address (before.trans_le floor))
      (TrieWalk.Graph.PathFields.of_prefix graph target.memory nodeLower heap.toNat regions memory)
      (by intro address _safe before; exact memory address before) tags
      next members rootMember nextValues nextRegions nextDisjoint nextPaths nextPathRegions nextSeparated provenance protection

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.extension_prefix_output
