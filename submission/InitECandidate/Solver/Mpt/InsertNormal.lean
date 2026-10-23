import InitECandidate.Solver.Mpt.InsertLoopNormal
import InitECandidate.Solver.Mpt.InsertLoopModelInitial
import InitECandidate.Solver.Mpt.TrieGraphPathErase

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole unchanged251 normal insertion: derive all real iterations,
parent stores and scope exits. The actual returned root is registered in
the complete current graph, with bounded values, full path lifetimes and
all older graph members/tags and persistent-prefix words preserved. -/
theorem body_path_normal (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size) (empty : property 0#64 0#64) (floor : nodeLower≤heap.toNat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
      (∀ current,graph.valid current → current≠0#64 → wordAt target.memory current=wordAt source.memory current) ∧
      ∃ root finalHeap : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,graph.valid current → next.valid current) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧ graph.PathFields target.memory ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat → target.memory address=source.memory address) := by
  obtain ⟨initial,initialMembers,initialHeap⟩:=initial_loop_model source heap node key level length pointer size graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated query member nodeCell keyCell levelCell lengthCell pointerCell sizeCell before bounded payload floor domain installed heapCell frontier aligned
  obtain ⟨inner,clock,frame,continued⟩:=normal_setup source target value normal
  rw [loop_shape] at continued
  have safe : Input.LocalPrefix (ofString "klen") (.while test loopBody):=.loop test loop_body_safe
  obtain ⟨last,loopRun,returnRun⟩:=Input.sequence_returned (setup source) inner (.while test loopBody) (.return (localVar "result")) value
    (fun returned=>(safe.summary_full (setup source)).2.1 returned) continued
  obtain ⟨finished,stopped,grows,members,memory,tags,fields,protectedWords⟩:=loop_path_normal (setup source) last key length pointer size limit nodeLower pathLower property initial extra empty loopRun
  obtain ⟨read,innerEq⟩:=Input.return_normal last inner (localVar "result") value returnRun
  have expected : eval last (localVar "result")=some (.val (.word finished.result)):=by
    simp [eval,evalHOLExact,toExact,localVar,finished.resultCell]
  have answer : value=.val (.word finished.result):=Option.some.inj (read.symm.trans expected)
  rw [innerEq] at frame
  change Input.LocalEffects.erase target=Input.LocalEffects.erase last at frame
  have memoryEq:=Input.LocalEffects.memory_of_erase last target frame
  have globalsEq:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=last.globals at globalsEq
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    finished.graph.after_erase last target limit nodeLower finished.heap.toNat pathLower finished.heap.toNat property finished.values finished.regions finished.disjoint finished.paths finished.pathRegions finished.separated frame
  have inclusion (current : BitVec 64) (live : graph.valid current) : next.valid current:=by
    rw [same]
    exact members current (by rw [initialMembers]; exact live)
  have preserved (query : BitVec 64) (before : query.toNat<nodeLower) : target.memory query=source.memory query:=
    (congrFun memoryEq query).trans (memory query before)
  have finalTags (current : BitVec 64) (live : graph.valid current) (active : current≠0#64) : wordAt target.memory current=wordAt source.memory current:=by
    rw [memoryEq]
    exact tags current (by rw [initialMembers]; exact live) active
  have finalHeapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word finished.heap)):=by rw [globalsEq]; exact finished.heapCell
  have heapGrows : heap.toNat≤finished.heap.toNat:=by rw [←initialHeap]; exact grows
  have evaluatedFields:=Input.evaluation_fields source target body (some (.returned value)) normal
  refine ⟨evaluatedFields.1,evaluatedFields.2.1,evaluatedFields.2.2.2,preserved,finalTags,finished.result,finished.heap,answer,finalHeapCell,finished.heapArena,finished.heapAligned,heapGrows,
    next,inclusion,(by rw [same]; exact finished.resultMember),nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,?_,?_⟩
  · rw [memoryEq]
    have initialFields : graph.PathFields (setup source).memory:=⟨by intro node live active; rfl,by intro node live active tag; exact ⟨rfl,rfl⟩⟩
    exact initialFields.trans graph initial.graph fields (by intro node live; rw [initialMembers]; exact live)
  · intro address safe before
    rw [memoryEq]
    have initialFields : graph.PathFields (setup source).memory:=⟨by intro node live active; rfl,by intro node live active tag; exact ⟨rfl,rfl⟩⟩
    have initialSafe:=safe.of_fields graph initial.graph address initialMembers initialFields
    exact protectedWords address (fun _=>initialSafe) (by rw [initialHeap]; exact before)

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.body_path_normal
