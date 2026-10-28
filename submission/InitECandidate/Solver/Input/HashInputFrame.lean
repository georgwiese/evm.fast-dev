import Guest.Model
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace InitECandidate.Solver.Input.HashInput
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Agreement with actual copied/decoded memory on one fixed physical
input region. The upper frontier is fixed before hashing, not each nested
callee's later temporary heap. No future outcome or digest fact is included. -/
structure Frame (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) : Prop where
  words : ∀ query : BitVec 64,lower≤query.toNat → query.toNat<upper → current.memory query=origin.memory query

theorem Frame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) : Frame source source lower upper := ⟨by intro query low high; rfl⟩

theorem Frame.trans (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (first : Frame origin source lower upper) (next : Frame source target lower upper) : Frame origin target lower upper :=
  ⟨by intro query low high; exact (next.words query low high).trans (first.words query low high)⟩

theorem Frame.of_memory (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (current : Frame origin source lower upper) (same : target.memory=source.memory) : Frame origin target lower upper :=
  ⟨by intro query low high; rw [same]; exact current.words query low high⟩

theorem Frame.at_callee (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (lower upper : Nat)
    (current : Frame origin source lower upper) : Frame origin (callEntryStateHOLFinite source callee) lower upper := ⟨current.words⟩

theorem Frame.cell (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (current : Frame origin source lower upper) (query value : BitVec 64) (low : lower≤query.toNat) (high : query.toNat<upper)
    (stored : origin.memory query=.word value) : source.memory query=.word value := (current.words query low high).trans stored

end InitECandidate.Solver.Input.HashInput

#print axioms InitECandidate.Solver.Input.HashInput.Frame.refl
#print axioms InitECandidate.Solver.Input.HashInput.Frame.trans
#print axioms InitECandidate.Solver.Input.HashInput.Frame.of_memory
#print axioms InitECandidate.Solver.Input.HashInput.Frame.at_callee
#print axioms InitECandidate.Solver.Input.HashInput.Frame.cell
