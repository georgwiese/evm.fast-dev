import InitECandidate.Solver.MutableTable.SetModelPost
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

theorem ModelPost.heap_globals {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind}
    {old plan : Plan} {start count paid : Nat} {globals : HolFiniteMapExact MlS (ValueHOL 64)} {memory : WordWrites.Memory} {slots : List Nat}
    (post : ModelPost source kind old start count paid globals memory target plan slots) : HeapGlobals source target := by
  have frame := congrArg PanSemStateFiniteExact.globals post.frame
  change target.globals = globals at frame
  intro key different
  rw [frame]
  rcases post.shape with ⟨_, same⟩ | ⟨_, same⟩
  · rw [same]
  · rw [same]
    exact HeapGlobals.update source _ key different

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.heap_globals
