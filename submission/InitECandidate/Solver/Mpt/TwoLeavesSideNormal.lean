import InitECandidate.Solver.Mpt.TwoLeavesSideOutput
import InitECandidate.Solver.Mpt.TwoLeavesLeafSide
import InitECandidate.Solver.Mpt.TwoLeavesZero

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both actual original side cases preserve the complete current graph
and both borrowed buffers. Their actual normal output supplies its heap. -/
theorem side_normal (second : Bool) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key length pointer size otherKey otherLength branch : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (otherBuffer : graph.PathBuffer source.be pathLower heap.toNat otherKey otherLength.toNat)
    (floor : nodeLower≤heap.toNat)
    (keyCell : source.locals.lookup (ofString (label second "k1" "k2"))=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString (label second "l1" "l2"))=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString (label second "v1" "v2"))=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString (label second "vl1" "vl2"))=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (branchMember : graph.valid branch) (branchActive : branch≠0#64) (tag : wordAt source.memory branch=3#64)
    (normal : evaluateHOLFiniteState source (choice second)=(none,post)) :
    Nonempty (SideOutput source post graph heap key length otherKey otherLength branch limit nodeLower pathLower property) := by
  by_cases zero : length=0#64
  · subst length
    obtain ⟨run,next,same,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=
      zero_side_paths second source branch pointer size graph limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated
        branchMember branchActive tag lengthCell branchCell pointerCell sizeCell payload extra
    have postEq : post=BranchValueUpdate.post source branch pointer size:=congrArg Prod.snd (normal.symm.trans run)
    subst post
    have notHash : wordAt source.memory branch≠0#64:=by rw [tag]; decide
    have notLeaf : wordAt source.memory branch≠1#64:=by rw [tag]; decide
    have notExtension : wordAt source.memory branch≠2#64:=by rw [tag]; decide
    have first:=buffer.after_branch_value_update source graph nodeLower heap.toNat pathLower heap.toNat key (0#64).toNat regions disjoint
      branch pointer size branchMember branchActive notHash notLeaf notExtension next same
    have other:=otherBuffer.after_branch_value_update source graph nodeLower heap.toNat pathLower heap.toNat otherKey otherLength.toNat regions disjoint
      branch pointer size branchMember branchActive notHash notLeaf notExtension next same
    have away:=graph.branch_value_away nodeLower heap.toNat regions disjoint branch branch branchMember branchActive notHash notLeaf notExtension (.header branch branchMember branchActive)
    have branchTag : wordAt (BranchValueUpdate.post source branch pointer size).memory branch=3#64:=by
      unfold wordAt
      rw [BranchValueUpdate.post_away source branch pointer size branch away.1 away.2]
      exact tag
    have prefixMemory (query : BitVec 64) (before : query.toNat<branch.toNat) : (BranchValueUpdate.post source branch pointer size).memory query=source.memory query:=by
      have arena:=(regions branch branchMember branchActive).2.1
      have away (offset : Nat) (inside : offset<176) : query≠byteAddress branch offset:=by
        intro equal
        have fits : branch.toNat+offset<2^64:=by
          have bound:=arena.upper
          have size : TrieWalk.nodeBytes (wordAt source.memory branch)=176:=by simp [tag,TrieWalk.nodeBytes]
          rw [size] at bound
          omega
        have number:=congrArg BitVec.toNat equal
        rw [byteAddress_toNat branch offset fits] at number
        omega
      exact BranchValueUpdate.post_away source branch pointer size query (away 160 (by decide)) (away 168 (by decide))
    exact ⟨{
      heap:=heap
      locals:=rfl
      domain:=rfl
      endian:=rfl
      code:=rfl
      heapCell:=heapCell
      heapArena:=frontier
      heapAligned:=aligned
      heapGrows:=Nat.le_refl _
      branchTag:=branchTag
      olderPrefix:=prefixMemory
      graph:=next
      oldMember:=by intro node member; rw [same]; exact member
      branchMember:=by rw [same]; exact branchMember
      values:=nextValues
      regions:=nextRegions
      disjoint:=nextDisjoint
      paths:=nextPaths
      pathRegions:=nextPathRegions
      separated:=nextSeparated
      buffer:=first
      otherBuffer:=other }⟩
  · have positive : 0<length.toNat:=by
      by_contra bad
      have numeric : length.toNat=(0#64).toNat:=by change length.toNat=0; omega
      exact zero (BitVec.toNat_inj.mp numeric)
    have leafRun : evaluateHOLFiniteState source (leafScope second)=(none,post):=(nonzero_choice second source length zero lengthCell).symm.trans normal
    obtain ⟨localsEq,domainEq,endianEq,codeEq,nextHeapCell,nextArena,nextAligned,grows,nextTag,prefixMemory,next,members,nextBranch,nextLeaf,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated,first,other⟩:=
      leaf_side_paths second source post heap key length pointer size otherKey otherLength branch graph limit nodeLower pathLower property
        values regions disjoint paths pathRegions separated buffer otherBuffer positive floor keyCell lengthCell pointerCell sizeCell payload extra domain heapCell frontier aligned installed
        branchCell branchMember branchActive tag leafRun
    exact ⟨{
      heap:=PersistentAlloc.rounded heap 64#64
      locals:=localsEq
      domain:=domainEq
      endian:=endianEq
      code:=codeEq
      heapCell:=nextHeapCell
      heapArena:=nextArena
      heapAligned:=nextAligned
      heapGrows:=grows
      branchTag:=nextTag
      olderPrefix:=prefixMemory
      graph:=next
      oldMember:=fun node member=>(members node).mpr (Or.inl member)
      branchMember:=nextBranch
      values:=nextValues
      regions:=nextRegions
      disjoint:=nextDisjoint
      paths:=nextPaths
      pathRegions:=nextPathRegions
      separated:=nextSeparated
      buffer:=first
      otherBuffer:=other }⟩

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.side_normal
