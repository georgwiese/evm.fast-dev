import InitECandidate.Solver.Mpt.DeleteExtensionMergeNormal
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole unchanged253 normal contract, covering null, retained branch
child and actual path merge. Every result is registered in the current
closed graph with all original members, values and full path models. -/
theorem body_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node child segment length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (segmentBuffer : graph.PathBuffer source.be pathLower heap.toNat segment length.toNat) (floor : 2701131776≤pathLower)
    (nodeFloor : nodeLower≤heap.toNat) (positive : 0<length.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64) (childMember : graph.valid child)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (lengthCell : source.locals.lookup (ofString "sl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      source.clock-target.clock≤length.toNat/8+(wordAt source.memory (child+40#64)).toNat/8+22 ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧ graph.PathFields target.memory ∧
      ∃ root finalHeap : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ (graph.valid root ∨ heap.toNat≤root.toNat) ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,graph.valid current → next.valid current) ∧ (∀ current,next.valid current ↔ graph.valid current ∨ current=root) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  by_cases null : child=0#64
  · subst child
    obtain ⟨answer,endpoint⟩:=null_normal source target childCell value normal
    rw [endpoint]
    exact ⟨rfl,rfl,rfl,by change source.clock-source.clock≤_; omega,fun _ _=>rfl,
      TrieWalk.Graph.PathFields.of_agreement graph source.memory (fun _ _=>rfl),
      0#64,heap,answer,heapCell,frontier,aligned,Nat.le_refl _,Or.inl graph.null,
      graph,fun _ old=>old,(fun current=>⟨Or.inl,fun choice=>choice.elim id (fun same=>same.symm ▸ graph.null)⟩),graph.null,regions,disjoint,⟨values⟩,paths,pathRegions,separated⟩
  · obtain ⟨inner,continued,endpoint⟩:=tag_entry source target child graph childMember null childCell value normal
    let entered:=QueryBranch.bind source "ck" (wordAt source.memory child)
    have enteredNode : entered.locals.lookup (ofString "node")=some (.val (.word node)):=
      (bind_lookup_other source "ck" "node" _ (by decide)).trans nodeCell
    have enteredSegment : entered.locals.lookup (ofString "seg")=some (.val (.word segment)):=
      (bind_lookup_other source "ck" "seg" _ (by decide)).trans segmentCell
    have enteredLength : entered.locals.lookup (ofString "sl")=some (.val (.word length)):=
      (bind_lookup_other source "ck" "sl" _ (by decide)).trans lengthCell
    have enteredChild : entered.locals.lookup (ofString "nc")=some (.val (.word child)):=
      (bind_lookup_other source "ck" "nc" _ (by decide)).trans childCell
    have enteredTag : entered.locals.lookup (ofString "ck")=some (.val (.word (wordAt entered.memory child))):=bind_lookup_same _ _ _
    by_cases branch : wordAt source.memory child=3#64
    · have enteredBranch : wordAt entered.memory child=3#64:=branch
      rw [branch_dispatch entered _ enteredTag,if_pos enteredBranch] at continued
      obtain ⟨answer,innerEq,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
        branch_finish_paths entered inner node child graph limit nodeLower heap.toNat pathLower property values regions disjoint paths pathRegions separated
          member active tag childMember enteredNode enteredChild value continued
      subst inner
      rw [endpoint]
      have addressNumber : (node+48#64).toNat=node.toNat+48:=BitVec.toNat_add_of_lt (by
        change node.toNat+48<2^64
        have upper:=(regions node member active).2.1.upper
        rw [tag] at upper
        change node.toNat+56≤33806089496 at upper
        omega)
      have before (query : BitVec 64) (lower : query.toNat<nodeLower) :
          (branchPost entered node child).memory query=source.memory query:=by
        change StoreWord.put source.memory (node+48#64) child query=source.memory query
        apply if_neg
        intro same
        have number:=congrArg BitVec.toNat same
        rw [addressNumber] at number
        have floor:=(regions node member active).1
        omega
      have fields : graph.PathFields (branchPost entered node child).memory:=
        TrieWalk.Graph.PathFields.of_child_store graph nodeLower heap.toNat regions disjoint node child 48 (.extension tag) member active
      have exactMembers (current : BitVec 64) : next.valid current ↔ graph.valid current ∨ current=node:=by
        rw [same]
        exact ⟨Or.inl,fun choice=>choice.elim id (fun same=>same.symm ▸ member)⟩
      exact ⟨rfl,rfl,rfl,by change source.clock-source.clock≤_; omega,before,fields,node,heap,answer,heapCell,frontier,aligned,Nat.le_refl _,Or.inl member,next,
        (fun current old=>by rw [same]; exact old),exactMembers,(by rw [same]; exact member),nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩
    · obtain ⟨pathTag,mergeRun⟩:=merge_entry entered inner child graph childMember null enteredTag branch installed value continued
      obtain ⟨domainEq,endianEq,codeEq,price,older,root,finalHeap,answer,finalCell,finalArena,finalAligned,grows,fresh,
        next,members,exactMembers,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
        merge_paths entered inner heap child segment length graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated segmentBuffer floor nodeFloor positive
          childMember null pathTag enteredSegment enteredLength enteredChild enteredTag heapCell frontier aligned little domain installed value mergeRun
      rw [endpoint]
      have fields : graph.PathFields inner.memory:=TrieWalk.Graph.PathFields.of_prefix graph inner.memory nodeLower heap.toNat regions older
      exact ⟨domainEq,endianEq,codeEq,price,(fun query before=>older query (by omega)),fields,root,finalHeap,answer,finalCell,finalArena,finalAligned,grows,Or.inr fresh,
        next,members,exactMembers,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.body_path_normal
