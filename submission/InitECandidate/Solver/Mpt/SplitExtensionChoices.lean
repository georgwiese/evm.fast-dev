import InitECandidate.Solver.Mpt.SplitExtensionOldSide
import InitECandidate.Solver.Mpt.SplitExtensionNewRemainder

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem old_single_prefix : Input.LocalPrefix (ofString "br") oldSingleChoice := by
  rw [old_shapes.2.2.1,oldChildStore]
  exact .ite _ (.store _ _) .skip

theorem old_long_prefix : Input.LocalPrefix (ofString "br") oldLongChoice := by
  rw [old_shapes.2.2.2.1,old_shapes.2.2.2.2,oldExtensionStore]
  exact .ite _ (.decCall _ _ _ _ (by decide) (.store _ _)) .skip

theorem choices_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap branch segment prefixLength remaining child key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat (segment+prefixLength) remaining.toNat)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (queryBound : prefixLength.toNat≤length.toNat)
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (positive : 0<remaining.toNat) (floor : nodeLower≤heap.toNat)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (remainingCell : source.locals.lookup (ofString "sal")=some (.val (.word remaining)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (branchMember : graph.valid branch) (branchActive : branch≠0#64) (tag : wordAt source.memory branch=3#64) (childMember : graph.valid child)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source oldChoices=(some (.returned value),target)) :
    value=.val (.word branch) ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<branch.toNat → target.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ wordAt target.memory branch=3#64 ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,
          (∀ node,graph.valid node → next.valid node) ∧ next.valid branch ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway (segment+prefixLength) remaining.toNat address → TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) := by
  rw [old_shapes.1] at normal
  obtain ⟨middle,firstRun,afterFirst,_⟩:=old_single_prefix.normal_continue source target afterSingle value normal
  rw [old_shapes.2.1] at afterFirst
  obtain ⟨last,secondRun,continued,_⟩:=old_long_prefix.normal_continue middle target newRemainderScope value afterFirst
  have sideRun : evaluateHOLFiniteState source oldSide=(none,last):=by
    rw [oldSide,evaluateHOLFiniteState_seq_line780,firstRun]
    exact secondRun
  obtain ⟨output⟩:=old_side_normal source last heap branch segment prefixLength remaining child key length graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated buffer query positive floor branchCell segmentCell prefixCell remainingCell childCell
    branchMember branchActive tag childMember domain heapCell frontier aligned installed sideRun
  have current (name : MlS) : last.locals.lookup name=source.locals.lookup name:=by rw [output.locals]
  have currentInstalled : Input.OriginalCode.Installed last.code:=by rw [output.code]; exact installed
  obtain ⟨answer,domainEq,endianEq,codeEq,memory,finalHeap,finalHeapCell,finalArena,finalAligned,grows,finalTag,next,members,member,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,finalFresh,finalProtection⟩:=
    new_remainder_normal last target output.heap branch key prefixLength length pointer size (segment+prefixLength) remaining output.graph limit nodeLower pathLower property
      output.values output.regions output.disjoint output.paths output.pathRegions output.separated output.otherBuffer queryBound output.buffer (floor.trans output.heapGrows)
      ((current _).trans branchCell) ((current _).trans keyCell) ((current _).trans prefixCell) ((current _).trans lengthCell)
      ((current _).trans pointerCell) ((current _).trans sizeCell) (by rw [output.domain]; exact payload) extra
      output.branchMember branchActive output.branchTag (output.domain.trans domain) output.heapCell output.heapArena output.heapAligned currentInstalled value continued
  have prefixMemory (query : BitVec 64) (before : query.toNat<branch.toNat) : target.memory query=source.memory query:=
    (memory query before).trans (output.olderPrefix query before)
  have provenance (current : BitVec 64) (live : next.valid current) : graph.valid current ∨ heap.toNat≤current.toNat:=by
    rcases finalFresh current live with old|fresh
    · exact output.freshMembers current old
    · exact Or.inr (output.heapGrows.trans fresh)
  have protection (address : BitVec 64) (safe : graph.ProtectedWord address) (before : address.toNat<heap.toNat)
      (oldAway : TrieWalk.PathWordAway (segment+prefixLength) remaining.toNat address) (queryAway : TrieWalk.PathWordAway key length.toNat address) : next.ProtectedWord address:=by
    exact finalProtection address (output.protectedGraph address safe before oldAway) (before.trans_le output.heapGrows) queryAway
  exact ⟨answer,domainEq.trans output.domain,endianEq.trans output.endian,codeEq.trans output.code,prefixMemory,
    finalHeap,finalHeapCell,finalArena,finalAligned,output.heapGrows.trans grows,finalTag,next,
    (fun node live=>members node (output.oldMember node live)),member,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,provenance,protection⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.old_single_prefix
#print axioms InitECandidate.Solver.Mpt.SplitExtension.old_long_prefix
#print axioms InitECandidate.Solver.Mpt.SplitExtension.choices_normal
