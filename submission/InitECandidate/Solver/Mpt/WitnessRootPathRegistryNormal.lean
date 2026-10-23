import InitECandidate.Solver.Mpt.WitnessRootPathNormal
import InitECandidate.Solver.Mpt.WitnessPathRegistryJoin

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors WitnessCore

/-- Successful original240 materialization retains every caller node and
adds the actual decoded result, with real value bounds and disjoint
allocation extents at the actual final heap. -/
theorem registered_path_body_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor scratchLimit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (arena : Rlp.Validation.Arena source cursor scratchLimit) (below : cursor.toNat≤2713717616)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2713731432≤pointer.toNat)
    (little : source.be=false)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post))
    (old : TrieWalk.Graph source.memory source.memaddrs) (floor pathLower limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values old limit property) (regions : old.Regions floor heap.toNat) (disjoint : old.Disjoint)
    (bytes : old.PathBytes source.be) (pathRegions : old.PathRegions pathLower heap.toNat) (pathSeparated : old.PathSeparated)
    (pathAbove : 2713717616+7≤pathLower) (pathOrdered : pathLower≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (above : 2713717616≤floor) (ordered : floor≤heap.toNat) (bounded : 1024≤limit)
    (extra : ∀ pointer length,WitnessValue db pointer length → property pointer length) :
    ∃ nextHeap node,returned=.val (.word node) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      ∃ graph : TrieWalk.Graph post.memory post.memaddrs,
        Nonempty (TrieWalk.Values graph limit property) ∧ graph.Regions floor nextHeap.toNat ∧ graph.Disjoint ∧
        graph.PathBytes post.be ∧ graph.PathRegions pathLower nextHeap.toNat ∧ graph.PathSeparated ∧
        (∀ child,old.valid child → graph.valid child) ∧ graph.valid node := by
  have result:=path_body_normal_prefix input source post db pointer length heap cursor scratchLimit boundary dbCell pointerCell lengthCell heapCell heapLower arena below before small lower little installed returned normal
  exact result.1.join_registry_paths input source post db heap returned floor pathLower limit result.2.2
    (Input.evaluation_fields source post body (some (.returned returned)) normal).1
    (Input.evaluation_fields source post body (some (.returned returned)) normal).2.1 old property values regions disjoint bytes pathRegions pathSeparated pathAbove pathOrdered heapAligned above ordered bounded extra

end InitECandidate.Solver.Mpt.WitnessMaterialize

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors WitnessMaterialize WitnessCore

/-- Whole original241 normal return with an arbitrary currently live
caller graph: both its old nodes and the exact returned root belong to
the resulting bounded closed graph. No graph is supplied for a future state. -/
theorem registered_path_body_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap root emptyRoot : BitVec 64) (boundary : RootBoundary input source)
    (little : source.be=false)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (emptyCell : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post))
    (old : TrieWalk.Graph source.memory source.memaddrs) (floor pathLower limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values old limit property) (regions : old.Regions floor heap.toNat) (disjoint : old.Disjoint)
    (bytes : old.PathBytes source.be) (pathRegions : old.PathRegions pathLower heap.toNat) (pathSeparated : old.PathSeparated)
    (pathAbove : 2713717616+7≤pathLower) (pathOrdered : pathLower≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (above : 2713717616≤floor) (ordered : floor≤heap.toNat) (bounded : 1024≤limit)
    (extra : ∀ pointer length,WitnessValue db pointer length → property pointer length) :
    ∃ nextHeap node,returned=.val (.word node) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      ∃ graph : TrieWalk.Graph post.memory post.memaddrs,
        Nonempty (TrieWalk.Values graph limit property) ∧ graph.Regions floor nextHeap.toNat ∧ graph.Disjoint ∧
        graph.PathBytes post.be ∧ graph.PathRegions pathLower nextHeap.toNat ∧ graph.PathSeparated ∧
        (∀ child,old.valid child → graph.valid child) ∧ graph.valid node := by
  have result:=path_body_normal_prefix input source post db heap root emptyRoot boundary little installed dbCell rootCell emptyCell heapCell heapLower scratch returned normal
  exact result.1.join_registry_paths input source post db heap returned floor pathLower limit result.2
    (Input.evaluation_fields source post body (some (.returned returned)) normal).1
    (Input.evaluation_fields source post body (some (.returned returned)) normal).2.1 old property values regions disjoint bytes pathRegions pathSeparated pathAbove pathOrdered heapAligned above ordered bounded extra

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.registered_path_body_normal
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.registered_path_body_normal
