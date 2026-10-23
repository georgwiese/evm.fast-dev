import InitECandidate.Solver.Mpt.TriePathBuffer

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget

theorem Graph.PathBuffer.weaken {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (be : Bool) (lower upper smaller larger : Nat) (pointer : BitVec 64) (length : Nat)
    (buffer : graph.PathBuffer be lower upper pointer length) (first : smaller≤lower) (last : upper≤larger) :
    graph.PathBuffer be smaller larger pointer length :=
  ⟨buffer.span,⟨first.trans buffer.bounds.1,buffer.bounds.2.trans last⟩,buffer.apart⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.weaken
