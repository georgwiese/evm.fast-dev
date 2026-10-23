import InitECandidate.Solver.Mpt.DeleteFrameOwnership
import InitECandidate.Solver.Mpt.TriePathBuffer
import InitECandidate.Solver.Mpt.TrieProtectedWord

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Results derived from the actual original unwind choice. It changes
only res in the caller and retains every saved older parent descriptor. -/
structure ChoiceOutput (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (heap : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop) where
  root : BitVec 64
  finalHeap : BitVec 64
  locals : target.locals=source.locals.update (ofString "res",.val (.word root))
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  globals : ∀ key,key≠ofString "heap_ptr"→target.globals.lookup key=source.globals.lookup key
  memory : ∀ query : BitVec 64,query.toNat<nodeLower→target.memory query=source.memory query
  fields : graph.PathFields target.memory
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap))
  heapArena : AllocatedBytes.Arena finalHeap 0
  heapAligned : finalHeap.toNat%8=0
  grows : heap.toNat≤finalHeap.toNat
  fresh : graph.valid root ∨ heap.toNat≤root.toNat
  next : TrieWalk.Graph target.memory target.memaddrs
  members : ∀ current,next.valid current ↔ graph.valid current ∨ current=root
  rootMember : next.valid root
  regions : next.Regions nodeLower finalHeap.toNat
  disjoint : next.Disjoint
  values : TrieWalk.Values next limit property
  paths : next.PathBytes target.be
  pathRegions : next.PathRegions pathLower finalHeap.toNat
  separated : next.PathSeparated
  protectedWords : ∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
    target.memory address=source.memory address ∧ next.ProtectedWord address

theorem ChoiceOutput.old_member (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (heap : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (output : ChoiceOutput source target graph heap limit nodeLower pathLower property)
    (node : BitVec 64) (member : graph.valid node) : output.next.valid node :=
  (output.members node).2 (Or.inl member)

theorem ChoiceOutput.parents (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (heap : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (output : ChoiceOutput source target graph heap limit nodeLower pathLower property)
    (frames : List DeleteFrame.Saved) (parents : DeleteFrame.Parents graph frames) : DeleteFrame.Parents output.next frames :=
  parents.of_fields graph output.next frames (output.old_member source target graph heap limit nodeLower pathLower property) output.fields

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.ChoiceOutput.old_member
#print axioms InitECandidate.Solver.Mpt.DeleteBody.ChoiceOutput.parents
