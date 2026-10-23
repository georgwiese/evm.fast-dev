import InitECandidate.Solver.Mpt.DeleteUnwindBranch
import InitECandidate.Solver.Mpt.DeleteUnwindExtension
import InitECandidate.Solver.Mpt.DeleteUnwindModelChoice

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

theorem unwind_choice_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (saved : DeleteFrame.Saved)
    (view : saved.View source) (owned : saved.Owned model.graph) (topEq : model.top=saved.pointer)
    (nodeCell : source.locals.lookup (ofString "fnode")=some (.val (.word saved.node)))
    (normal : evaluateHOLFiniteState source unwindChoice=(none,target)) :
    Nonempty (ChoiceOutput source target model.graph model.heap limit nodeLower pathLower property) := by
  have topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer)):=by rw [←topEq]; exact model.topCell
  have floor : 2701131776≤pathLower:=(by decide : 2701131776≤DeleteFrame.ceiling).trans model.floor
  cases kindEq : saved.kind with
  | extension=>
    exact unwind_extension_normal source target saved model.result model.heap model.graph limit nodeLower pathLower property
      model.values model.regions model.disjoint model.paths model.pathRegions model.separated view owned kindEq model.resultMember floor model.nodeFloor
      topCell nodeCell model.resultCell model.heapCell model.heapArena model.heapAligned model.little model.scratch.domain model.installed normal
  | branch=>
    exact unwind_branch_normal source target saved model.result model.heap model.graph limit nodeLower pathLower property
      model.values model.regions model.disjoint model.paths model.pathRegions model.separated view owned kindEq model.resultMember floor model.pathFloor model.nodeFloor
      topCell nodeCell model.resultCell model.heapCell model.heapArena model.heapAligned model.little model.scratch.domain model.installed normal

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_choice_normal
