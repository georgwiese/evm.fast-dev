import InitECandidate.Solver.Mpt.TrieGraphChildStore
import InitECandidate.Solver.Input.WordStoreNormal

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact GasBudget WitnessRadix

/-- Join the physical child update to the actual word store, with its
real caller expressions. Normal execution derives the write and mapping. -/
theorem Graph.child_store_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (owner child : BitVec 64) (offset : Nat) (slot : ChildSlot source.memory owner offset)
    (ownerMember : graph.valid owner) (ownerActive : owner≠0#64) (childMember : graph.valid child)
    (destination expression : ExpHOL 64)
    (addressRead : QueryBranch.eval source destination=some (.val (.word (owner+BitVec.ofNat 64 offset))))
    (childRead : QueryBranch.eval source expression=some (.val (.word child)))
    (normal : evaluateHOLFiniteState source (.store destination expression)=(none,target)) :
    ∃ next : Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  obtain ⟨mapped,post⟩:=Input.word_store_normal source target destination expression (owner+BitVec.ofNat 64 offset) child addressRead childRead normal
  subst target
  exact graph.after_child_store source limit lower upper pathLower pathUpper property values regions disjoint paths pathRegions separated owner child offset slot ownerMember ownerActive childMember

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.child_store_normal
