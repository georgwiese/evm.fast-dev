import InitECandidate.Solver.Mpt.InsertAfterHashOutput
import InitECandidate.Solver.Mpt.InsertHashGuardNormal
import InitECandidate.Solver.Mpt.InsertNodeOutputScope
import InitECandidate.Solver.Mpt.TrieWalkRead
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_kind_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source) (member : graph.valid node) (active : node≠0#64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word (wordAt source.memory node))))
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source afterKind=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  rw [dispatch_shapes.2.1] at normal
  obtain ⟨middle,guardRun,continued⟩:=Input.sequence_none source target hashGuard afterHash normal
  obtain ⟨middleEq,notHash⟩:=hash_guard_normal source middle (wordAt source.memory node) tagCell installed guardRun
  subst middle
  exact after_hash_output source target heap node key level length pointer size graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated query pending member active notHash tagCell nodeCell keyCell levelCell lengthCell pointerCell sizeCell
    before bounded payload extra floor empty domain installed heapCell frontier aligned continued

/-- Whole nonempty original251 dispatch: derive its actual mapped tag
load and failing-hash exclusion, real invalidation and kind case, then
restore the temporary tag binding at the genuine node-choice exit. -/
theorem nonempty_output_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source) (member : graph.valid node) (active : node≠0#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source nonemptyChoice=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  have header:=graph.header node member active
  have read : eval source (nodeFieldExpression 0#64)=some (.val (.word (wordAt source.memory node))):=by
    simpa only [nodeFieldExpression,TrieWalk.nodeField,BitVec.add_zero] using TrieWalk.node_field_read source node 0#64 (wordAt source.memory node) nodeCell
      (by simpa only [BitVec.add_zero] using header.1) (by simpa only [BitVec.add_zero] using header.2)
  rw [dispatch_shapes.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "k" (nodeFieldExpression 0#64) (wordAt source.memory node) afterKind read normal
  let ready:=QueryBranch.bind source "k" (wordAt source.memory node)
  have current (name : String) (other : ofString "k"≠ofString name) : ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    bind_lookup_other source "k" name _ other
  have currentPending:=pending.after_scalar source ready "k" (wordAt source.memory node) (by decide) (by decide) (by decide) (by decide) rfl
  obtain ⟨output⟩:=after_kind_output ready inner heap node key level length pointer size graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated query currentPending member active (bind_lookup_same source "k" _)
    ((current _ (by decide)).trans nodeCell) ((current _ (by decide)).trans keyCell) ((current _ (by decide)).trans levelCell) ((current _ (by decide)).trans lengthCell)
    ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell) before bounded payload extra floor empty domain installed heapCell frontier aligned continued
  rw [endpoint]
  exact output.restore_scope source ready inner graph graph heap key length level limit nodeLower pathLower property "k" (wordAt source.memory node)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.after_kind_output
#print axioms InitECandidate.Solver.Mpt.Insert.nonempty_output_normal
