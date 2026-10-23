import InitECandidate.Solver.Mpt.CollapseBranchChildEntry
import InitECandidate.Solver.Mpt.CollapseBranchNibbleCost

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_kind_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap index child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower maximum : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated) (pathLimit : graph.PathLimit maximum)
    (lower : pathLower≤heap.toNat) (floor : 2701131776≤pathLower) (bounded : index.toNat<16) (member : graph.valid child) (active : child≠0#64)
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word index)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterKind).2.clock≤maximum/8+23 := by
  by_cases hash : wordAt source.memory child=0#64
  · let failure : ProgHOL 64:=.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]
    have chosen : evaluateHOLFiniteState source hashGuard=evaluateHOLFiniteState source failure:=by
      rw [child_shapes.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,hash,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,failure]
    have stops : (evaluateHOLFiniteState source hashGuard).1≠none:=by
      rw [chosen]
      intro normal
      exact Fail.call_not_normal source _ installed _ (Prod.ext normal rfl)
    rw [child_shapes.2.2.1,Input.sequence_stopped source hashGuard nibbleScope stops,chosen]
    have price:=Fail.call_price source.code installed [.const 2#64] source rfl
    change source.clock-(evaluateHOLFiniteState source failure).2.clock≤1 at price
    omega
  · have skipped : evaluateHOLFiniteState source hashGuard=(none,source):=by
      rw [child_shapes.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,hash,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [child_shapes.2.2.1,StateSteps.next_sequence source source hashGuard nibbleScope skipped (Nat.le_refl _)]
    have price:=nibble_cost source heap index child graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated lower floor bounded member active hash
      indexCell childCell tagCell heapCell frontier aligned little domain installed
    have boundedPrice:=after_store_price_limit graph maximum pathLimit child member active hash
    omega

/-- All outcomes of the original selected-child and ck scopes, priced
from the actual scan slot, real child/header reads and current path limit. -/
theorem single_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node index : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower maximum : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated) (pathLimit : graph.PathLimit maximum)
    (lower : pathLower≤heap.toNat) (floor : 2701131776≤pathLower)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word index))) (bounded : index.toNat<16)
    (selectedNonzero : wordAt source.memory (node+32#64+index*8#64)≠0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source childScope).2.clock≤maximum/8+23 := by
  let view:=graph.branch node member active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide) index.toNat bounded
  have product : BitVec.ofNat 64 (index.toNat*8)=index*8#64:=by rw [BitVec.ofNat_mul]; simp
  have mapped : source.memaddrs (node+32#64+index*8#64):=by simpa only [product] using view.mapped
  have stored : source.memory (node+32#64+index*8#64)=.word view.child:=by simpa only [product] using view.stored
  have number : wordAt source.memory (node+32#64+index*8#64)=view.child:=by simp [wordAt,stored,MemoryBytes.wordBits]
  have childActive : view.child≠0#64:=by rwa [number] at selectedNonzero
  have read:=selected_read source node index view.child nodeCell indexCell mapped stored
  let selected:=QueryBranch.bind source "child" view.child
  let entered:=QueryBranch.bind selected "ck" (wordAt source.memory view.child)
  have selectedChild : selected.locals.lookup (ofString "child")=some (.val (.word view.child)):=bind_lookup_same _ _ _
  obtain ⟨headerMapped,headerStored⟩:=graph.header view.child view.member childActive
  have tagRead : eval selected (field "child" 0#64)=some (.val (.word (wordAt source.memory view.child))):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read selected "child" view.child 0#64 _ selectedChild
      (by simpa only [selected,QueryBranch.bind,setVarHOLFinite,BitVec.add_zero] using headerMapped)
      (by simpa only [selected,QueryBranch.bind,setVarHOLFinite,BitVec.add_zero] using headerStored)
  have currentIndex : entered.locals.lookup (ofString "idx")=some (.val (.word index)):=
    (bind_lookup_other selected "ck" "idx" _ (by decide)).trans ((bind_lookup_other source "child" "idx" view.child (by decide)).trans indexCell)
  have currentChild : entered.locals.lookup (ofString "child")=some (.val (.word view.child)):=
    (bind_lookup_other selected "ck" "child" _ (by decide)).trans selectedChild
  have currentTag : entered.locals.lookup (ofString "ck")=some (.val (.word (wordAt entered.memory view.child))):=bind_lookup_same _ _ _
  have price:=after_kind_cost entered heap index view.child graph limit nodeLower pathLower maximum property values regions disjoint paths pathRegions separated pathLimit lower floor bounded view.member childActive
    currentIndex currentChild currentTag heapCell frontier aligned little domain installed
  have kindPrice : selected.clock-(evaluateHOLFiniteState selected kindScope).2.clock≤maximum/8+23:=by
    rw [child_shapes.2.1]
    exact Input.ClockCost.declared_current selected "ck" (field "child" 0#64) (wordAt source.memory view.child) afterKind _ tagRead price
  rw [child_shapes.1]
  exact Input.ClockCost.declared_current source "child" (.load .one (childAddress (localVar "idx"))) view.child kindScope _ read kindPrice

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.after_kind_cost
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.single_cost
