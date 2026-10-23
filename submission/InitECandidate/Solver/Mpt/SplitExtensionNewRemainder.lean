import InitECandidate.Solver.Mpt.SplitExtensionNewSide
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem new_choice_prefix : Input.LocalPrefix (ofString "br") newChoice := by
  rw [new_shapes.2.2.1,new_shapes.2.2.2.1,new_shapes.2.2.2.2.1,new_shapes.2.2.2.2.2.1,new_shapes.2.2.2.2.2.2.1,BranchValueUpdate.stores,newLeafStore]
  apply Input.LocalPrefix.ite
  · exact .seq (.store _ _) (.store _ _)
  · apply Input.LocalPrefix.dec
    · decide
    · apply Input.LocalPrefix.seq
      · apply Input.LocalPrefix.ite
        · exact .call none _ _ (by intro name impossible; cases impossible)
        · exact .skip
      · exact .decCall _ _ _ _ (by decide) (.store _ _)

theorem new_remainder_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap branch key prefixLength length pointer size otherKey otherLength : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (bound : prefixLength.toNat≤length.toNat)
    (query : graph.PathBuffer source.be pathLower heap.toNat otherKey otherLength.toNat)
    (floor : nodeLower≤heap.toNat)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (remainingCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (branchMember : graph.valid branch) (branchActive : branch≠0#64) (tag : wordAt source.memory branch=3#64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source newRemainderScope=(some (.returned value),target)) :
    value=.val (.word branch) ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<branch.toNat → target.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ wordAt target.memory branch=3#64 ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,
          (∀ node,graph.valid node → next.valid node) ∧ next.valid branch ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) := by
  have subtraction : (length-prefixLength).toNat=length.toNat-prefixLength.toNat:=BitVec.toNat_sub_of_le (by rwa [BitVec.le_def])
  have suffix:=buffer.window graph source.be pathLower heap.toNat key prefixLength length.toNat (length-prefixLength).toNat bound (by rw [subtraction])
  have read : eval source newRemainder=some (.val (.word (length-prefixLength))):=by
    simp [newRemainder,eval,evalHOLExact,toExact,localVar,remainingCell,prefixCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [new_shapes.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source target "kal" newRemainder (length-prefixLength) afterNewRemainder value read normal
  let ready:=QueryBranch.bind source "kal" (length-prefixLength)
  rw [new_shapes.2.1] at continued
  obtain ⟨last,executed,footerRun,branchPreserved⟩:=new_choice_prefix.normal_continue ready inner footer value continued
  have current (name : String) (other : ofString "kal"≠ofString name) : ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    bind_lookup_other source "kal" name _ other
  have currentRemaining : ready.locals.lookup (ofString "kal")=some (.val (.word (length-prefixLength))):=bind_lookup_same source "kal" _
  obtain ⟨output⟩:=new_side_normal ready last heap branch key prefixLength (length-prefixLength) pointer size otherKey otherLength
    graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated suffix query floor
      ((current _ (by decide)).trans branchCell) ((current _ (by decide)).trans keyCell) ((current _ (by decide)).trans prefixCell)
      currentRemaining ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell)
      payload extra branchMember branchActive tag domain heapCell frontier aligned installed executed
  rw [new_shapes.2.2.2.2.2.2.2] at footerRun
  obtain ⟨observed,innerEq⟩:=Input.return_normal last inner (localVar "br") value footerRun
  have lastBranch : last.locals.lookup (ofString "br")=some (.val (.word branch)):=branchPreserved.trans ((current _ (by decide)).trans branchCell)
  have expected : eval last (localVar "br")=some (.val (.word branch)):=by simp [eval,localVar,evalHOLExact,toExact,lastBranch]
  have answer : value=.val (.word branch):=Option.some.inj (observed.symm.trans expected)
  rw [endpoint,innerEq]
  exact ⟨answer,output.domain,output.endian,output.code,output.olderPrefix,output.heap,output.heapCell,output.heapArena,output.heapAligned,
    output.heapGrows,output.branchTag,output.graph,output.oldMember,output.branchMember,output.regions,output.disjoint,⟨output.values⟩,output.paths,output.pathRegions,output.separated,output.freshMembers,
    (by
      intro address safe before away
      exact output.protectedGraph address safe before (away.window key prefixLength address length.toNat _ bound (by rw [subtraction])))⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.new_choice_prefix
#print axioms InitECandidate.Solver.Mpt.SplitExtension.new_remainder_normal
