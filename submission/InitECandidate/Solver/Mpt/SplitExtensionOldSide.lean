import InitECandidate.Solver.Mpt.SplitExtensionOldExtension

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Sequential composition of the two actual old-side statements. -/
def oldSide : ProgHOL 64:=.seq oldSingleChoice oldLongChoice

/-- A positive old remainder either attaches its genuine existing child
or constructs a positive extension. Both actual outcomes retain the closed
graph, full buffers, caller bindings and older-memory frame. -/
theorem old_side_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap branch segment prefixLength remaining child key length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat (segment+prefixLength) remaining.toNat)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
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
    (normal : evaluateHOLFiniteState source oldSide=(none,target)) :
    Nonempty (TwoLeaves.ProtectedSideOutput source target graph heap (segment+prefixLength) remaining key length branch limit nodeLower pathLower property) := by
  by_cases one : remaining=1#64
  · obtain ⟨index,small,stored,tags,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
      old_store_paths source branch child segment prefixLength "child" remaining.toNat buffer.span positive branchCell segmentCell prefixCell childCell
        graph limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated branchMember branchActive tag childMember
    let changed:={source with memory:=StoreWord.put source.memory (branch+BitVec.ofNat 64 (32+index*8)) child}
    have selected : evaluateHOLFiniteState source oldSingleChoice=evaluateHOLFiniteState source oldChildStore:=by
      rw [old_shapes.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,remainingCell,one,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have firstRun : evaluateHOLFiniteState source oldSingleChoice=(none,changed):=selected.trans stored
    have currentRemaining : changed.locals.lookup (ofString "sal")=some (.val (.word remaining)):=remainingCell
    have lastRun : evaluateHOLFiniteState changed oldLongChoice=(none,changed):=by
      rw [old_shapes.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,currentRemaining,one,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    have run : evaluateHOLFiniteState source oldSide=(none,changed):=by rw [oldSide,evaluateHOLFiniteState_seq_line780,firstRun]; exact lastRun
    have targetEq : target=changed:=congrArg Prod.snd (normal.symm.trans run)
    subst target
    have notHash : wordAt source.memory branch≠0#64:=by rw [tag]; decide
    have notLeaf : wordAt source.memory branch≠1#64:=by rw [tag]; decide
    have notExtension : wordAt source.memory branch≠2#64:=by rw [tag]; decide
    have slot : TrieWalk.ChildSlot source.memory branch (32+index*8):=.branch notHash notLeaf notExtension index small
    have first:=buffer.after_child_store source graph pathLower heap.toNat (segment+prefixLength) remaining.toNat branch child (32+index*8) slot branchMember branchActive next same tags
    have other:=query.after_child_store source graph pathLower heap.toNat key length.toNat branch child (32+index*8) slot branchMember branchActive next same tags
    have prefixMemory (query : BitVec 64) (before : query.toNat<branch.toNat) : changed.memory query=source.memory query:=by
      have arena:=(regions branch branchMember branchActive).2.1
      have within:=(slot.bounds source.memory branch (32+index*8)).2.2.1
      have away : query≠branch+BitVec.ofNat 64 (32+index*8):=by
        intro equal
        have number:=congrArg BitVec.toNat equal
        change query.toNat=(byteAddress branch (32+index*8)).toNat at number
        rw [byteAddress_toNat branch (32+index*8) (by have upper:=arena.upper; omega)] at number
        omega
      exact if_neg away
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
      branchTag:=(tags branch branchMember branchActive).trans tag
      olderPrefix:=prefixMemory
      graph:=next
      oldMember:=by intro node live; rw [same]; exact live
      freshMembers:=by intro node live; rw [same] at live; exact Or.inl live
      protectedGraph:=by
        intro address safe _before _away
        exact safe.of_fields graph next address same
          (TrieWalk.Graph.PathFields.of_child_store graph nodeLower heap.toNat regions disjoint branch child (32+index*8) slot branchMember branchActive)
      branchMember:=by rw [same]; exact branchMember
      values:=Classical.choice nextValues
      regions:=nextRegions
      disjoint:=nextDisjoint
      paths:=nextPaths
      pathRegions:=nextPathRegions
      separated:=nextSeparated
      buffer:=first
      otherBuffer:=other }⟩
  · have large : 1<remaining.toNat:=by
      by_contra bad
      have number : remaining.toNat=(1#64).toNat:=by change remaining.toNat=1; omega
      exact one (BitVec.toNat_inj.mp number)
    have wordLarge : (1#64 : BitVec 64)<remaining:=by rw [BitVec.lt_def]; change 1<remaining.toNat; exact large
    have firstRun : evaluateHOLFiniteState source oldSingleChoice=(none,source):=by
      rw [old_shapes.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,remainingCell,one,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [oldSide,evaluateHOLFiniteState_seq_line780,firstRun] at normal
    have selected : evaluateHOLFiniteState source oldLongChoice=evaluateHOLFiniteState source oldExtensionScope:=by
      rw [old_shapes.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,remainingCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,wordLarge]
    have continued : evaluateHOLFiniteState source oldExtensionScope=(none,target):=selected.symm.trans normal
    exact old_extension_normal source target heap branch segment prefixLength remaining child key length graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated buffer query large floor branchCell segmentCell prefixCell remainingCell childCell
      branchMember branchActive tag childMember domain heapCell frontier aligned installed continued

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.old_side_normal
