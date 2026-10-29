import InitECandidate.Solver.Mpt.InsertIterationEntry
import InitECandidate.Solver.Mpt.InsertLoopModel

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real cleared iteration prefix satisfies every current input of the
checked original node choice; no successful future graph is a premise. -/
theorem dispatch_output (source chosen : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key length pointer size : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (model : LoopModel source key length pointer size limit nodeLower pathLower property) (active : model.go≠0#64)
    (extra : property pointer size) (empty : property 0#64 0#64)
    (normal : evaluateHOLFiniteState (dispatchEntry source) nodeChoice=(none,chosen)) :
    Nonempty (NodeOutput (dispatchEntry source) chosen model.graph model.heap key length model.level limit nodeLower pathLower property) := by
  have current (name : String) (notRoot : ofString name≠ofString "r") (notNode : ofString name≠ofString "next_node")
      (notSlot : ofString name≠ofString "next_slot") (notLevel : ofString name≠ofString "next_level") (notGo : ofString name≠ofString "go") :
      (dispatchEntry source).locals.lookup (ofString name)=source.locals.lookup (ofString name):=dispatch_saved source name notRoot notNode notSlot notLevel notGo
  exact node_choice_output (dispatchEntry source) chosen model.heap model.node key model.level length pointer size model.graph limit nodeLower pathLower property
    model.values model.regions model.disjoint model.paths model.pathRegions model.separated (model.query active) (Pending.dispatch source) model.nodeMember
    ((current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.nodeCell)
    ((current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.keyCell)
    ((current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.levelCell)
    ((current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.lengthCell)
    ((current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.pointerCell)
    ((current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans model.sizeCell)
    (model.activeBound active) model.bounded model.payload extra model.floor empty model.domain model.installed model.heapCell model.heapArena model.heapAligned normal

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.dispatch_saved
#print axioms InitECandidate.Solver.Mpt.Insert.dispatch_output
