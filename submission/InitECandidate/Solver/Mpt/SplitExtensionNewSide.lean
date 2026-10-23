import InitECandidate.Solver.Mpt.SplitExtensionNewNonzero
import InitECandidate.Solver.Mpt.BranchValueUpdateGraph
import InitECandidate.Solver.Mpt.TriePathFieldsMutation

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem new_side_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap branch key prefixLength remaining pointer size otherKey otherLength : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat (key+prefixLength) remaining.toNat)
    (query : graph.PathBuffer source.be pathLower heap.toNat otherKey otherLength.toNat)
    (floor : nodeLower≤heap.toNat)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (remainingCell : source.locals.lookup (ofString "kal")=some (.val (.word remaining)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (branchMember : graph.valid branch) (branchActive : branch≠0#64) (tag : wordAt source.memory branch=3#64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source newChoice=(none,target)) :
    Nonempty (TwoLeaves.ProtectedSideOutput source target graph heap (key+prefixLength) remaining otherKey otherLength branch limit nodeLower pathLower property) := by
  by_cases zero : remaining=0#64
  · subst remaining
    have notHash : wordAt source.memory branch≠0#64:=by rw [tag]; decide
    have notLeaf : wordAt source.memory branch≠1#64:=by rw [tag]; decide
    have notExtension : wordAt source.memory branch≠2#64:=by rw [tag]; decide
    let old:=values.branch branch branchMember branchActive notHash notLeaf notExtension
    have selected : evaluateHOLFiniteState source newChoice=evaluateHOLFiniteState source (BranchValueUpdate.stores "br" "vptr" "vlen"):=by
      rw [new_shapes.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,remainingCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have run:=selected.trans (BranchValueUpdate.stores_execute source branch pointer size "br" "vptr" "vlen"
      branchCell pointerCell sizeCell old.pointerMapped old.lengthMapped)
    obtain ⟨next,same,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=
      graph.after_branch_value_update source branch pointer size limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated
        branchMember branchActive notHash notLeaf notExtension payload extra
    have targetEq : target=BranchValueUpdate.post source branch pointer size:=congrArg Prod.snd (normal.symm.trans run)
    subst target
    have first:=buffer.after_branch_value_update source graph nodeLower heap.toNat pathLower heap.toNat (key+prefixLength) (0#64).toNat regions disjoint
      branch pointer size branchMember branchActive notHash notLeaf notExtension next same
    have other:=query.after_branch_value_update source graph nodeLower heap.toNat pathLower heap.toNat otherKey otherLength.toNat regions disjoint
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
      freshMembers:=by intro node live; rw [same] at live; exact Or.inl live
      protectedGraph:=by
        intro address safe _before _away
        exact safe.of_fields graph next address same
          (TrieWalk.Graph.PathFields.of_branch_value source branch pointer size graph nodeLower heap.toNat regions disjoint branchMember branchActive notHash notLeaf notExtension)
      branchMember:=by rw [same]; exact branchMember
      values:=nextValues
      regions:=nextRegions
      disjoint:=nextDisjoint
      paths:=nextPaths
      pathRegions:=nextPathRegions
      separated:=nextSeparated
      buffer:=first
      otherBuffer:=other }⟩
  · have positive : 0<remaining.toNat:=by
      by_contra bad
      have number : remaining.toNat=(0#64).toNat:=by change remaining.toNat=0; omega
      exact zero (BitVec.toNat_inj.mp number)
    have selected : evaluateHOLFiniteState source newChoice=evaluateHOLFiniteState source newNonzeroScope:=by
      rw [new_shapes.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,remainingCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact new_nonzero_normal source target heap branch key prefixLength remaining pointer size otherKey otherLength graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated buffer query positive floor branchCell keyCell prefixCell remainingCell pointerCell sizeCell
      payload extra branchMember branchActive tag domain heapCell frontier aligned installed (selected.symm.trans normal)

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.new_side_normal
