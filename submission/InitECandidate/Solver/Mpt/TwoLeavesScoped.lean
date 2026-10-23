import InitECandidate.Solver.Mpt.TwoLeavesNormal
import InitECandidate.Solver.Mpt.TwoLeavesEnvironment
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual scoped original248 call retains the complete graph/path
contract at its genuine caller continuation, with its source-clock allowance. -/
theorem scoped_path_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key1 length1 pointer1 size1 key2 length2 pointer2 size2 : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer1 : graph.PathBuffer source.be pathLower heap.toNat key1 length1.toNat)
    (buffer2 : graph.PathBuffer source.be pathLower heap.toNat key2 length2.toNat)
    (payload1 : TrieWalk.Payload source.memaddrs pointer1 size1 limit) (extra1 : property pointer1 size1)
    (payload2 : TrieWalk.Payload source.memaddrs pointer2 size2 limit) (extra2 : property pointer2 size2)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (TwoLeaves.values key1 length1 pointer1 size1 key2 length2 pointer2 size2))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "_create_branch_from_two_leaves") arguments continuation)=(some (.returned value),post)) :
    ∃ ready inner,ready.locals.lookup (ofString name)=some (.val (.word heap)) ∧
      ready.locals=source.locals.update (ofString name,.val (.word heap)) ∧ ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      source.clock-ready.clock≤236 ∧ evaluateHOLFiniteState ready continuation=(some (.returned value),inner) ∧ post=restore source name inner ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,ready.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ wordAt ready.memory heap=3#64 ∧
        ∃ next : TrieWalk.Graph ready.memory ready.memaddrs,
          (∀ node,graph.valid node → next.valid node) ∧ next.valid heap ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes ready.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          next.PathBuffer ready.be pathLower finalHeap.toNat key1 length1.toNat ∧ next.PathBuffer ready.be pathLower finalHeap.toNat key2 length2.toNat ∧
          (∀ node,next.valid node → graph.valid node ∨ heap.toNat≤node.toNat) ∧
          (∀ query : BitVec 64,graph.ProtectedWord query → query.toNat<heap.toNat →
            TrieWalk.PathWordAway key1 length1.toNat query → TrieWalk.PathWordAway key2 length2.toNat query → next.ProtectedWord query) := by
  obtain ⟨callee,called,inputs1,inputs2⟩:=environment source key1 length1 pointer1 size1 key2 length2 pointer2 size2 (original_code source.code installed)
  obtain ⟨funded,target,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post name .one
    (ofString "_create_branch_from_two_leaves") arguments (TwoLeaves.values key1 length1 pointer1 size1 key2 length2 pointer2 size2)
    body continuation callee .one argsRead called value normal
  obtain ⟨answer,domainEq,endianEq,codeEq,prefixMemory,finalHeap,nextHeapCell,nextArena,nextAligned,grows,branchTag,next,oldMember,branchMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,first,other,provenance,protection⟩:=
    body_path_normal (callEntryStateHOLFinite source callee) target heap key1 length1 pointer1 size1 key2 length2 pointer2 size2 graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated buffer1 buffer2 inputs1 inputs2 payload1 extra1 payload2 extra2 floor empty domain heapCell frontier aligned installed returned run
  let ready:=Input.CallNormal.continuationEntry source target name returned
  have localCell : ready.locals.lookup (ofString name)=some (.val (.word heap)):=by
    simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have localsEq : ready.locals=source.locals.update (ofString name,.val (.word heap)):=by
    simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite]
  have price:=(body_price source.code installed) (callEntryStateHOLFinite source callee) rfl
  rw [run] at price
  change source.clock-1-target.clock≤235 at price
  have clockEq : ready.clock=target.clock:=rfl
  have spent : source.clock-ready.clock≤236:=by rw [clockEq]; omega
  exact ⟨ready,inner,localCell,localsEq,domainEq,endianEq,codeEq,spent,continued,endpoint,prefixMemory,finalHeap,nextHeapCell,nextArena,nextAligned,grows,branchTag,
    next,oldMember,branchMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,first,other,provenance,protection⟩

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.scoped_path_normal
