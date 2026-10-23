import InitECandidate.Solver.Mpt.DeleteUnwindBranch
import InitECandidate.Solver.Mpt.DeleteUnwindModel
import InitECandidate.Solver.Mpt.DeleteExtensionPhysicalCost
import InitECandidate.Solver.Input.ClockCostAssignedCurrent

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All outcomes of the genuine saved-parent choice. Byte-copy work is
bounded by current actual path extents; no future helper success or next
registry is supplied. Branch replacement is executed before its collapse. -/
theorem unwind_choice_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (saved : DeleteFrame.Saved)
    (view : saved.View source) (owned : saved.Owned model.graph) (topEq : model.top=saved.pointer)
    (nodeCell : source.locals.lookup (ofString "fnode")=some (.val (.word saved.node))) :
    source.clock-(evaluateHOLFiniteState source unwindChoice).2.clock≤2*((model.heap.toNat-pathLower)/8)+40 := by
  have topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer)):=by rw [←topEq]; exact model.topCell
  have floor : 2701131776≤pathLower:=(by decide : 2701131776≤DeleteFrame.ceiling).trans model.floor
  cases kindEq : saved.kind with
  | extension=>
    have args:=extension_arguments source saved model.result view kindEq model.scratch.domain topCell nodeCell model.resultCell
    obtain ⟨buffer,_positive⟩:=owned.extension_buffer source saved model.graph pathLower model.heap.toNat kindEq model.paths model.pathRegions model.separated
    obtain ⟨callee,called,_nodeCell,segmentCell,lengthCell,childCell⟩:=Input.word_quad_environment source.code.lookup (ofString "_delete_ext_finish")
      (ofString "node") (ofString "seg") (ofString "sl") (ofString "nc") DeleteExtension.body .one saved.node (saved.words "seg") (saved.words "sl") model.result
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (DeleteExtension.original_code source.code model.installed)
    have priced:=DeleteExtension.body_physical_cost (callEntryStateHOLFinite source callee) model.heap model.result (saved.words "seg") (saved.words "sl") model.graph pathLower
      model.pathRegions buffer floor model.resultMember segmentCell lengthCell childCell model.heapCell model.heapArena model.scratch.domain model.installed
    have callerPrice:=Input.ClockCost.assigned_current source (some (.local,ofString "res")) (ofString "_delete_ext_finish") extensionArguments _ DeleteExtension.body callee .one
      ((saved.words "sl").toNat/8+(model.heap.toNat-pathLower)/8+22) args called priced
    have lengthBound : (saved.words "sl").toNat≤model.heap.toNat-pathLower:=by have bounds:=buffer.bounds; omega
    have quotient : (saved.words "sl").toNat/8≤(model.heap.toNat-pathLower)/8:=Nat.div_le_div_right lengthBound
    rw [unwind_dispatch source saved view model.scratch.domain topCell,kindEq]
    exact callerPrice.trans (by omega)
  | branch=>
    obtain ⟨executed,_storeMemory,storeFields,current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated⟩:=
      branch_child_store source saved model.result model.graph limit nodeLower model.heap.toNat pathLower property model.values model.regions model.disjoint model.paths model.pathRegions model.separated
        view owned kindEq model.resultMember topCell nodeCell model.resultCell model.scratch.domain
    let post:=branchPost source saved model.result
    have args : evalListHOLFinite post (h:=fun query=>Classical.propDecidable (post.memaddrs query)) branchArguments=some [.val (.word saved.node)]:=by
      simp [branchArguments,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,show post.locals.lookup (ofString "fnode")=some (.val (.word saved.node)) from nodeCell]
    have member : current.valid saved.node:=by rw [same]; exact owned.1
    have oldTag : wordAt source.memory saved.node=3#64:=by simpa only [kindEq,DeleteFrame.Kind.tag] using owned.2.2.1
    have tag : wordAt post.memory saved.node=3#64:=(storeFields.tags saved.node owned.1 owned.2.1).trans oldTag
    obtain ⟨callee,called,calleeNode⟩:=CollapseBranch.environment post saved.node (CollapseBranch.original_code post.code model.installed)
    have priced:=CollapseBranch.body_cost (callEntryStateHOLFinite post callee) model.heap saved.node current limit nodeLower pathLower (model.heap.toNat-pathLower) property currentValues currentRegions currentDisjoint
      currentPaths currentPathRegions currentSeparated (TrieWalk.Graph.PathLimit.of_regions current pathLower model.heap.toNat currentPathRegions)
      (model.pathFloor.trans model.nodeFloor) floor member owned.2.1 tag calleeNode model.heapCell model.heapArena model.heapAligned model.little model.scratch.domain model.installed
    have callerPrice:=Input.ClockCost.assigned_current post (some (.local,ofString "res")) (ofString "_collapse_branch") branchArguments _ CollapseBranch.body callee .one
      ((model.heap.toNat-pathLower)/8+39) args called priced
    rw [unwind_dispatch source saved view model.scratch.domain topCell,kindEq,branchUnwind,
      StateSteps.next_sequence source post replaceChild finishBranch executed (Nat.le_refl _)]
    exact callerPrice.trans (by omega)

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_choice_cost
