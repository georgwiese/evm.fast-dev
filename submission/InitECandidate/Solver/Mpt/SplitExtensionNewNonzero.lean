import InitECandidate.Solver.Mpt.SplitExtensionNewLeaf
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Input.ScalarScope
import InitECandidate.Solver.Input.LoopNormal
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem collision_guard_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source collisionGuard=(none,target)) : target=source := by
  rw [new_shapes.2.2.2.2.2.1,evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) collisionTest=read at normal
  cases read with
  | none=>cases normal
  | some read=>
    cases read with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word word=>
        by_cases zero : word=0
        · have skipped : evaluateHOLFiniteState source .skip=(none,target):=by simpa only [if_pos zero] using normal
          exact (congrArg Prod.snd ((evaluateHOLFiniteState_skip source).symm.trans skipped)).symm
        · have failed : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mpt_fail") [.const 11#64])=(none,target):=by
            simpa only [if_neg zero] using normal
          exact (Fail.call_not_normal source target installed _ failed).elim

/-- The real nibble declaration and collision guard lead to the actual
new leaf. Normal execution itself excludes the failing collision branch. -/
theorem new_nonzero_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap branch key prefixLength remaining pointer size otherKey otherLength : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat (key+prefixLength) remaining.toNat)
    (query : graph.PathBuffer source.be pathLower heap.toNat otherKey otherLength.toNat)
    (positive : 0<remaining.toNat) (floor : nodeLower≤heap.toNat)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (remainingCell : source.locals.lookup (ofString "kal")=some (.val (.word remaining)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (branchMember : graph.valid branch) (branchActive : branch≠0#64) (tag : wordAt source.memory branch=3#64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source newNonzeroScope=(none,target)) :
    Nonempty (TwoLeaves.ProtectedSideOutput source target graph heap (key+prefixLength) remaining otherKey otherLength branch limit nodeLower pathLower property) := by
  obtain ⟨nibble,small,byteRead⟩:=buffer.span.nibble 0 positive
  have first : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (key+prefixLength)=some nibble:=by
    simpa only [byteAddress,BitVec.add_zero] using byteRead
  have read : eval source newIndex=some (.val (.word (BitVec.ofNat 64 nibble.toNat))):=by
    simp [newIndex,eval,evalHOLExact,toExact,localVar,keyCell,prefixCell,valueIsWord,valueWord,wordOpHOL,wordOp,evalListHOLExact,first]
  let bound:=QueryBranch.bind source "idx" (BitVec.ofNat 64 nibble.toNat)
  let output:=evaluateHOLFiniteState bound afterIndex
  have actual:=Input.ScalarScope.declare_execute source output.2 "idx" newIndex (BitVec.ofNat 64 nibble.toNat) afterIndex output.1 read rfl
  rw [new_shapes.2.2.2.1,actual] at normal
  have resultEq:=congrArg Prod.fst normal
  have endpoint : restore source "idx" output.2=target:=congrArg Prod.snd normal
  have run : evaluateHOLFiniteState bound afterIndex=(none,output.2):=Prod.ext resultEq rfl
  rw [new_shapes.2.2.2.2.1] at run
  obtain ⟨middle,guardRun,leafRun⟩:=Input.sequence_none bound output.2 collisionGuard newLeafScope run
  have middleEq:=collision_guard_none bound middle installed guardRun
  rw [middleEq] at leafRun
  have current (name : MlS) (other : name≠ofString "idx") : bound.locals.lookup name=source.locals.lookup name:=by
    simp [bound,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have indexCell : bound.locals.lookup (ofString "idx")=some (.val (.word (BitVec.ofNat 64 nibble.toNat))):=by
    simp [bound,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨leaf⟩:=new_leaf_normal bound output.2 heap branch key prefixLength remaining pointer size otherKey otherLength
    graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated buffer query positive nibble.toNat small floor
      ((current _ (by decide)).trans branchCell) ((current _ (by decide)).trans keyCell) ((current _ (by decide)).trans prefixCell)
      ((current _ (by decide)).trans remainingCell) ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell)
      indexCell payload extra branchMember branchActive tag domain heapCell frontier aligned installed leafRun
  have restoredLocals : (restore source "idx" output.2).locals=source.locals:=by
    change HolFiniteMapExact.resVarEq output.2.locals (ofString "idx",source.locals.lookup (ofString "idx"))=source.locals
    rw [leaf.locals]
    exact congrArg PanSemStateFiniteExact.locals (restore_bound source "idx" (BitVec.ofNat 64 nibble.toNat))
  rw [←endpoint]
  exact ⟨{ leaf with locals:=restoredLocals }⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.collision_guard_none
#print axioms InitECandidate.Solver.Mpt.SplitExtension.new_nonzero_normal
