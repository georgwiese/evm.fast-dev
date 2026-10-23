import InitECandidate.Solver.Mpt.TwoLeavesSideNormal
import InitECandidate.Solver.Mpt.TwoLeavesBranchEntry
import InitECandidate.Solver.Mpt.TwoLeavesInputs
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem side_prefix (second : Bool) : Input.LocalPrefix (ofString "br") (choice second) := by
  rw [(side_shapes second).1,(side_shapes second).2.1,(side_shapes second).2.2,BranchValueUpdate.stores]
  apply Input.LocalPrefix.ite
  · exact .seq (.store _ _) (.store _ _)
  · apply Input.LocalPrefix.decCall
    · cases second <;> decide
    · exact .store _ _

/-- Whole unchanged248: derive every fresh allocation and actual side
execution, return the genuine branch, and retain the full older graph and
both buffers. Every older persistent word survives this complete helper. -/
theorem body_path_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key1 length1 pointer1 size1 key2 length2 pointer2 size2 : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer1 : graph.PathBuffer source.be pathLower heap.toNat key1 length1.toNat)
    (buffer2 : graph.PathBuffer source.be pathLower heap.toNat key2 length2.toNat)
    (inputs1 : SideInputs source false key1 length1 pointer1 size1) (inputs2 : SideInputs source true key2 length2 pointer2 size2)
    (payload1 : TrieWalk.Payload source.memaddrs pointer1 size1 limit) (extra1 : property pointer1 size1)
    (payload2 : TrieWalk.Payload source.memaddrs pointer2 size2 limit) (extra2 : property pointer2 size2)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word heap) ∧ post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → post.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ wordAt post.memory heap=3#64 ∧
        ∃ next : TrieWalk.Graph post.memory post.memaddrs,
          (∀ node,graph.valid node → next.valid node) ∧ next.valid heap ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          next.PathBuffer post.be pathLower finalHeap.toNat key1 length1.toNat ∧ next.PathBuffer post.be pathLower finalHeap.toNat key2 length2.toNat := by
  obtain ⟨ready,inner,branchCell,localsEq,physical,codeEq,continued,endpoint,base,members,member,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated,first,other⟩:=
    branch_entry source post heap key1 length1 key2 length2 graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated buffer1 buffer2
      floor empty domain heapCell frontier aligned installed value normal
  have branchActive : heap≠0#64:=by
    intro zero
    have lower:=frontier.lower
    rw [zero] at lower
    change 2701131776≤0 at lower
    omega
  have currentTag : wordAt ready.memory heap=3#64:=by simp [wordAt,physical.tag,MemoryBytes.wordBits]
  have grows : heap.toNat≤(PersistentAlloc.rounded heap 176#64).toNat:=by
    have before : heap.toNat+176≤(PersistentAlloc.rounded heap 176#64).toNat:=physical.allocation.before
    omega
  have readyInstalled : Input.OriginalCode.Installed ready.code:=by rw [codeEq]; exact installed
  have firstInputs:=inputs1.after_branch source ready false key1 length1 pointer1 size1 heap localsEq
  have secondInputs:=inputs2.after_branch source ready true key2 length2 pointer2 size2 heap localsEq
  have firstRun : evaluateHOLFiniteState ready (.seq (choice false) afterFirst)=(some (.returned value),inner):=by
    change evaluateHOLFiniteState ready (.seq firstChoice afterFirst)=_
    rw [←program_shapes.2.1]
    exact continued
  obtain ⟨middle,firstExecuted,afterFirstRun,firstBranchCell⟩:=(side_prefix false).normal_continue ready inner afterFirst value firstRun
  obtain ⟨firstOutput⟩:=side_normal false ready middle (PersistentAlloc.rounded heap 176#64) key1 length1 pointer1 size1 key2 length2 heap base limit nodeLower pathLower property
    baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated first other (floor.trans grows)
    firstInputs.keyCell firstInputs.lengthCell firstInputs.pointerCell firstInputs.sizeCell
    (by rw [physical.allocation.domain]; exact payload1) extra1 (physical.allocation.domain.trans domain)
    physical.allocation.heapCell physical.allocation.nextArena physical.allocation.nextAligned readyInstalled branchCell member branchActive currentTag firstExecuted
  have nextInputs:=secondInputs.of_locals ready middle true key2 length2 pointer2 size2 firstOutput.locals
  have middleInstalled : Input.OriginalCode.Installed middle.code:=by rw [firstOutput.code]; exact readyInstalled
  have middleBranch : middle.locals.lookup (ofString "br")=some (.val (.word heap)):=by rw [firstOutput.locals]; exact branchCell
  have secondRun : evaluateHOLFiniteState middle (.seq (choice true) footer)=(some (.returned value),inner):=by
    change evaluateHOLFiniteState middle (.seq secondChoice footer)=_
    rw [←program_shapes.2.2.1]
    exact afterFirstRun
  obtain ⟨last,secondExecuted,footerRun,secondBranchCell⟩:=(side_prefix true).normal_continue middle inner footer value secondRun
  obtain ⟨secondOutput⟩:=side_normal true middle last firstOutput.heap key2 length2 pointer2 size2 key1 length1 heap firstOutput.graph limit nodeLower pathLower property
    firstOutput.values firstOutput.regions firstOutput.disjoint firstOutput.paths firstOutput.pathRegions firstOutput.separated firstOutput.otherBuffer firstOutput.buffer
    (floor.trans (grows.trans firstOutput.heapGrows)) nextInputs.keyCell nextInputs.lengthCell nextInputs.pointerCell nextInputs.sizeCell
    (by rw [firstOutput.domain,physical.allocation.domain]; exact payload2) extra2 ((firstOutput.domain.trans physical.allocation.domain).trans domain)
    firstOutput.heapCell firstOutput.heapArena firstOutput.heapAligned middleInstalled middleBranch firstOutput.branchMember branchActive firstOutput.branchTag secondExecuted
  rw [program_shapes.2.2.2] at footerRun
  obtain ⟨read,innerEq⟩:=Input.return_normal last inner (localVar "br") value footerRun
  have lastBranch : last.locals.lookup (ofString "br")=some (.val (.word heap)):=by rw [secondOutput.locals]; exact middleBranch
  have expected : eval last (localVar "br")=some (.val (.word heap)):=by simp [eval,localVar,evalHOLExact,toExact,lastBranch]
  have answer : value=.val (.word heap):=Option.some.inj (read.symm.trans expected)
  have prefixMemory (query : BitVec 64) (before : query.toNat<heap.toNat) : last.memory query=source.memory query:=
    (secondOutput.olderPrefix query before).trans ((firstOutput.olderPrefix query before).trans (physical.allocation.memory query (Or.inl before)))
  have oldMember (node : BitVec 64) (live : graph.valid node) : secondOutput.graph.valid node:=
    secondOutput.oldMember node (firstOutput.oldMember node ((members node).mpr (Or.inl live)))
  rw [endpoint,innerEq]
  exact ⟨answer,secondOutput.domain.trans (firstOutput.domain.trans physical.allocation.domain),secondOutput.endian.trans (firstOutput.endian.trans physical.allocation.endian),
    secondOutput.code.trans (firstOutput.code.trans codeEq),prefixMemory,secondOutput.heap,secondOutput.heapCell,secondOutput.heapArena,secondOutput.heapAligned,
    grows.trans (firstOutput.heapGrows.trans secondOutput.heapGrows),secondOutput.branchTag,secondOutput.graph,oldMember,secondOutput.branchMember,
    secondOutput.regions,secondOutput.disjoint,⟨secondOutput.values⟩,secondOutput.paths,secondOutput.pathRegions,secondOutput.separated,secondOutput.otherBuffer,secondOutput.buffer⟩

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.side_prefix
#print axioms InitECandidate.Solver.Mpt.TwoLeaves.body_path_normal
