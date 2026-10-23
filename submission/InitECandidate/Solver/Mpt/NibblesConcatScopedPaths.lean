import InitECandidate.Solver.Mpt.NibblesConcatPathGraph
import InitECandidate.Solver.Mpt.NibblesConcatCost
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real four-word ABI resumes its original continuation with the
fresh joined buffer, a complete retained trie, and the actual heap. -/
theorem scoped_normal_paths (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap a al b bl : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (values : TrieWalk.Values graph limit property)
    (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (left : graph.PathBuffer source.be pathLower heap.toNat a al.toNat)
    (right : graph.PathBuffer source.be pathLower heap.toNat b bl.toNat) (floor : 2701131776≤pathLower)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (callValues a al b bl))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "nibbles_concat") arguments continuation)=(some (.returned value),post)) :
    ∃ ready inner,ready.locals=source.locals.update (ofString name,.val (.word heap)) ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      source.clock-ready.clock≤al.toNat/8+bl.toNat/8+19 ∧
      evaluateHOLFiniteState ready continuation=(some (.returned value),inner) ∧ post=restore source name inner ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (al+bl)))) ∧
      AllocatedBytes.Arena (PersistentAlloc.rounded heap (al+bl)) 0 ∧ (PersistentAlloc.rounded heap (al+bl)).toNat%8=0 ∧
      heap.toNat+al.toNat+bl.toNat≤(PersistentAlloc.rounded heap (al+bl)).toNat ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query) ∧
      ∃ next : TrieWalk.Graph ready.memory ready.memaddrs,next.valid=graph.valid ∧
        next.Regions nodeLower (PersistentAlloc.rounded heap (al+bl)).toNat ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes ready.be ∧
        next.PathRegions pathLower (PersistentAlloc.rounded heap (al+bl)).toNat ∧ next.PathSeparated ∧
        next.PathBuffer ready.be pathLower (PersistentAlloc.rounded heap (al+bl)).toNat heap (al.toNat+bl.toNat) := by
  obtain ⟨callee,called,aCell,alCell,bCell,blCell⟩:=environment source a al b bl (original_code source.code installed)
  obtain ⟨_funded,target,returned,inner,run,_checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post name .one (ofString "nibbles_concat")
    arguments (callValues a al b bl) body continuation callee .one args called value normal
  obtain ⟨answer,heapResult,nextArena,nextAligned,grows,older,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,buffer⟩:=
    body_path_graph (callEntryStateHOLFinite source callee) target heap a al b bl graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated left right floor
      aCell alCell bCell blCell heapCell frontier aligned little domain installed returned run
  let ready:=Input.CallNormal.continuationEntry source target name returned
  have localsEq : ready.locals=source.locals.update (ofString name,.val (.word heap)):=by
    simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite]
  have sourceA : AllocatedBytes.Arena a al.toNat:=⟨floor.trans left.bounds.1,by have before:=left.bounds.2; have upper:=frontier.upper; omega⟩
  have sourceB : AllocatedBytes.Arena b bl.toNat:=⟨floor.trans right.bounds.1,by have before:=right.bounds.2; have upper:=frontier.upper; omega⟩
  have price:=body_cost (callEntryStateHOLFinite source callee) heap a al b bl sourceA sourceB aCell alCell bCell blCell heapCell frontier domain installed
  rw [run] at price
  change source.clock-1-target.clock≤al.toNat/8+bl.toNat/8+18 at price
  have spent : source.clock-ready.clock≤al.toNat/8+bl.toNat/8+19:=by change source.clock-target.clock≤_; omega
  have fields:=Input.evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned returned)) run
  exact ⟨ready,inner,localsEq,fields.1,fields.2.1,fields.2.2.2,spent,continued,endpoint,heapResult,nextArena,nextAligned,grows,older,
    next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,buffer⟩

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.scoped_normal_paths
