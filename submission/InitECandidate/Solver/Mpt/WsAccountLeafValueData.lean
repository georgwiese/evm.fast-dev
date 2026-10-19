import InitECandidate.Solver.Mpt.WsAccountLeafData
import InitECandidate.Solver.Mpt.TrieWalkValueHash

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem Data.values_after_hash (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs) (valueLimit : Nat) (values : TrieWalk.Values data.graph valueLimit)
    (protectedValues : TrieWalk.ValueProtected data.graph nibs)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (valueProtection : ∀ query,TrieWalk.ValueFootprint data.graph query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (control : KeccakAbsorb.hashControl post=KeccakAbsorb.hashControl source)
    (memory : ∀ query,Keccak256.Protected stp pad h query → post.memory query=source.memory query) :
    ∃ next : Data post ws root h nibs,TrieWalk.ValueProtected next.graph nibs ∧ Nonempty (TrieWalk.Values next.graph valueLimit) := by
  obtain ⟨next,validEq,nextProtection,nextValueProtection,⟨nextValues⟩⟩ := TrieWalk.Values.after_hash source post data.graph valueLimit values stp pad h nibs
    data.protectedGraph protectedValues graphProtection valueProtection control memory
  have globals := congrArg PanSemStateFiniteExact.globals control
  have domain := congrArg PanSemStateFiniteExact.memaddrs control
  have endian := congrArg PanSemStateFiniteExact.be control
  change post.globals=source.globals at globals
  change post.memaddrs=source.memaddrs at domain
  change post.be=source.be at endian
  exact ⟨{
    graph := next
    member := by rw [validEq]; exact data.member
    protectedGraph := nextProtection
    worldState := by rw [globals]; exact data.worldState
    rootMapped := by rw [domain]; exact data.rootMapped
    rootStored := (memory _ rootProtection).trans data.rootStored
    scratch := by rw [globals]; exact data.scratch
    little := endian.trans data.little
    fits := data.fits
    inputMapped := by simpa only [domain] using data.inputMapped
    outputMapped := by simpa only [domain] using data.outputMapped
    separate := data.separate },nextValueProtection,⟨nextValues⟩⟩

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.Data.values_after_hash
