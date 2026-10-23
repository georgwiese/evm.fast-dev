import InitECandidate.Solver.Mpt.DeleteDescentModel
import InitECandidate.Solver.Mpt.TrieProtectedWord

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- A genuine original descent dispatch outcome. Scratch pushes may
change the free low pool, so its frame protects memory below the caller
frame cursor and above the incoming scratch cursor, rather than falsely
claiming every word below persistent nodes is unchanged. -/
structure DescentOutput (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) where
  next : DescentModel target key length limit nodeLower pathLower property
  grows : model.pending.heap.toNat≤next.pending.heap.toNat
  scratchDecreases : next.pending.cursor.toNat≤model.pending.cursor.toNat
  frameEq : next.pending.frame=model.pending.frame
  members : ∀ node,model.pending.graph.valid node→next.pending.graph.valid node
  freshMembers : ∀ node,next.pending.graph.valid node→model.pending.graph.valid node ∨ model.pending.heap.toNat≤node.toNat
  fields : model.pending.graph.PathFields target.memory
  memoryLow : ∀ query : BitVec 64,query.toNat<model.pending.frame.toNat→target.memory query=source.memory query
  memoryBand : ∀ query : BitVec 64,model.pending.cursor.toNat≤query.toNat→query.toNat<nodeLower→target.memory query=source.memory query
  protectedWords : ∀ address : BitVec 64,model.pending.graph.ProtectedWord address →
    DeleteFrame.ceiling≤address.toNat → address.toNat<model.pending.heap.toNat →
    target.memory address=source.memory address ∧ next.pending.graph.ProtectedWord address
  globals : ∀ name,name≠ofString "heap_ptr"→name≠ofString "scratch_ptr"→target.globals.lookup name=source.globals.lookup name
  progress : next.go=0#64 ∨ model.level.toNat<next.level.toNat

end InitECandidate.Solver.Mpt.DeleteBody
