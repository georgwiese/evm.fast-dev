import InitECandidate.Solver.Mpt.InsertionHelperEnvironment
import InitECandidate.Solver.Mpt.SplitExtensionNormal
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scoped_none_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key length prefixLength pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64)
    (strict : prefixLength.toNat<(wordAt source.memory (node+40#64)).toNat)
    (queryBound : prefixLength.toNat≤length.toNat)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (callValues node key length pointer size prefixLength))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "_split_extension") arguments continuation)=(none,target)) :
    ∃ ready inner,ready.locals=source.locals.update (ofString name,.val (.word heap)) ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧ source.clock-ready.clock≤237 ∧
      evaluateHOLFiniteState ready continuation=(none,inner) ∧ target=restore source name inner ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,ready.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ wordAt ready.memory heap=3#64 ∧
        ∃ next : TrieWalk.Graph ready.memory ready.memaddrs,
          (∀ node,graph.valid node → next.valid node) ∧ next.valid heap ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes ready.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) := by
  obtain ⟨callee,called,nodeCell,keyCell,lengthCell,pointerCell,sizeCell,prefixCell⟩:=environment source node key length pointer size prefixLength (original_code source.code installed)
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none source target name .one
    (ofString "_split_extension") arguments (callValues node key length pointer size prefixLength) body continuation callee .one argsRead called normal
  obtain ⟨answer,domainEq,endianEq,codeEq,memory,finalHeap,finalHeapCell,finalArena,finalAligned,grows,finalTag,next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,provenance,protection⟩:=
    body_path_normal (callEntryStateHOLFinite source callee) child heap node key length prefixLength pointer size graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated
      query member active tag nodeCell keyCell lengthCell pointerCell sizeCell prefixCell strict queryBound payload extra floor empty domain heapCell frontier aligned installed returned run
  let ready:=Input.CallNormal.continuationEntry source child name returned
  have localsEq : ready.locals=source.locals.update (ofString name,.val (.word heap)):=by
    simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite]
  have price:=(body_price source.code installed) (callEntryStateHOLFinite source callee) rfl
  rw [run] at price
  change source.clock-1-child.clock≤236 at price
  have spent : source.clock-ready.clock≤237:=by change source.clock-child.clock≤237; omega
  exact ⟨ready,inner,localsEq,domainEq,endianEq,codeEq,spent,continued,endpoint,memory,finalHeap,finalHeapCell,finalArena,finalAligned,grows,finalTag,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,provenance,protection⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.scoped_none_paths
