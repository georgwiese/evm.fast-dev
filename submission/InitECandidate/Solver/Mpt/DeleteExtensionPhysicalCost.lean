import InitECandidate.Solver.Mpt.DeleteExtensionCost
import InitECandidate.Solver.Mpt.TriePathLimit

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Only a leaf/extension child can copy path bytes. Null, branch and
hash cases do not charge their unrelated or unmapped word at offset40. -/
theorem after_tag_physical_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap child segment length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (pathLower : Nat) (pathRegions : graph.PathRegions pathLower heap.toNat)
    (segmentBuffer : graph.PathBuffer source.be pathLower heap.toNat segment length.toNat) (floor : 2701131776≤pathLower)
    (member : graph.valid child) (active : child≠0#64)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (lengthCell : source.locals.lookup (ofString "sl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterTag).2.clock≤length.toNat/8+(heap.toNat-pathLower)/8+22 := by
  by_cases branch : wordAt source.memory child=3#64
  · rw [branch_dispatch source _ tagCell,if_pos branch]
    have price:=Input.ClockCost.of_quiet source.code branchFinish (branch_finish_quiet source.code) source rfl
    omega
  · by_cases hash : wordAt source.memory child=0#64
    · rw [branch_dispatch source _ tagCell,if_neg branch]
      let failure : ProgHOL 64:=.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]
      have chosen : evaluateHOLFiniteState source hashGuard=evaluateHOLFiniteState source failure:=by
        rw [merge_shapes.2.1,evaluateHOLFiniteState_ite]
        simp [evalHOLExact,toExact,localVar,tagCell,hash,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,failure]
      have stops : (evaluateHOLFiniteState source hashGuard).1≠none:=by
        rw [chosen]
        intro normal
        exact Fail.call_not_normal source (evaluateHOLFiniteState source failure).2 installed _ (Prod.ext normal rfl)
      rw [merge_shapes.1,Input.sequence_stopped source hashGuard concatScope stops,chosen]
      have price:=Fail.call_price source.code installed [.const 2#64] source rfl
      change source.clock-(evaluateHOLFiniteState source failure).2.clock≤1 at price
      omega
    · have tag:=graph.path_kind child member active hash branch
      have limit:=(TrieWalk.Graph.PathLimit.of_regions graph pathLower heap.toNat pathRegions) child member active tag
      have quotient : (wordAt source.memory (child+40#64)).toNat/8≤(heap.toNat-pathLower)/8:=Nat.div_le_div_right limit
      have price:=after_tag_cost source heap child segment length graph pathLower pathRegions segmentBuffer floor member active
        segmentCell lengthCell childCell tagCell heapCell frontier domain installed
      omega

/-- All outcomes of original253, bounded using the actual persistent
path extent. The only length charged for a child comes from its real path. -/
theorem body_physical_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap child segment length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (pathLower : Nat) (pathRegions : graph.PathRegions pathLower heap.toNat)
    (segmentBuffer : graph.PathBuffer source.be pathLower heap.toNat segment length.toNat) (floor : 2701131776≤pathLower)
    (member : graph.valid child)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (lengthCell : source.locals.lookup (ofString "sl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤length.toNat/8+(heap.toNat-pathLower)/8+22 := by
  by_cases null : child=0#64
  · subst child
    have guard : evaluateHOLFiniteState source nullGuard=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source):=by
      rw [entry_shapes.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,childCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,shapeOfHOLExact]
    rw [entry_shapes.1,StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) nullGuard tagScope (.returned (.val (.word 0#64))) guard (Nat.le_refl _)]
    change source.clock-source.clock≤_
    omega
  · have skipped : evaluateHOLFiniteState source nullGuard=(none,source):=by
      rw [entry_shapes.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,childCell,null,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [entry_shapes.1,StateSteps.next_sequence source source nullGuard tagScope skipped (Nat.le_refl _),entry_shapes.2.2.1]
    obtain ⟨mapped,stored⟩:=graph.header child member null
    have read : eval source (field "nc" 0#64)=some (.val (.word (wordAt source.memory child))):=
      field_read source "nc" child 0#64 _ childCell (by simpa only [BitVec.add_zero] using mapped) (by simpa only [BitVec.add_zero] using stored)
    let entered:=QueryBranch.bind source "ck" (wordAt source.memory child)
    have enteredSegment : entered.locals.lookup (ofString "seg")=some (.val (.word segment)):=
      (bind_lookup_other source "ck" "seg" _ (by decide)).trans segmentCell
    have enteredLength : entered.locals.lookup (ofString "sl")=some (.val (.word length)):=
      (bind_lookup_other source "ck" "sl" _ (by decide)).trans lengthCell
    have enteredChild : entered.locals.lookup (ofString "nc")=some (.val (.word child)):=
      (bind_lookup_other source "ck" "nc" _ (by decide)).trans childCell
    have enteredTag : entered.locals.lookup (ofString "ck")=some (.val (.word (wordAt entered.memory child))):=bind_lookup_same _ _ _
    have price:=after_tag_physical_cost entered heap child segment length graph pathLower pathRegions segmentBuffer floor member null
      enteredSegment enteredLength enteredChild enteredTag heapCell frontier domain installed
    exact Input.ClockCost.declared_current source "ck" (field "nc" 0#64) (wordAt source.memory child) afterTag _ read price

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.after_tag_physical_cost
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.body_physical_cost
