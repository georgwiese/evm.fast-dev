import InitECandidate.Solver.Mpt.SetOutput
import InitECandidate.Solver.Mpt.TrieProtectedFreshPath

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget

/-- The actual two-word map header, separate from all current node
allocations and stored path backing words, with its registered root. -/
structure Header (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (m root flag : BitVec 64) : Prop where
  arena : AllocatedBytes.Arena m 16
  aligned : m.toNat%8=0
  rootStored : source.memory m=.word root
  flagStored : source.memory (m+8#64)=.word flag
  member : graph.valid root
  rootSafe : graph.ProtectedWord m
  flagSafe : graph.ProtectedWord (m+8#64)

/-- The whole setter converts the key into a fresh buffer at its incoming
heap. Every older protected word therefore has the required path frame;
callers need no additional premise about a future query allocation. -/
theorem Output.older_word (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value : ValueHOL 64) (m incoming length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat)
    (property : BitVec 64→BitVec 64→Prop) (allowance : Nat)
    (output : Output source target value m graph incoming incoming length limit nodeLower pathLower property allowance)
    (frontier : AllocatedBytes.Arena incoming 0) (aligned : incoming.toNat%8=0) (small : length.toNat≤64)
    (address : BitVec 64) (safe : graph.ProtectedWord address)
    (above : DeleteFrame.ceiling≤address.toNat) (before : address.toNat<incoming.toNat) :
    (address≠m→target.memory address=source.memory address) ∧ output.next.ProtectedWord address := by
  have away:=TrieWalk.PathWordAway.above_frontier incoming address length.toNat incoming.toNat
    (by have upper:=frontier.upper; omega) aligned before (Nat.le_refl _)
  exact output.protectedWords address safe above before away

/-- Each successful real update retains the actual map's secure flag
and separation while installing its newly registered root. Headers may
lie between old nodes and nodes allocated by this update. -/
theorem Header.after_set (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value : ValueHOL 64) (m root flag incoming length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat)
    (property : BitVec 64→BitVec 64→Prop) (allowance : Nat)
    (header : Header source graph m root flag)
    (output : Output source target value m graph incoming incoming length limit nodeLower pathLower property allowance)
    (frontier : AllocatedBytes.Arena incoming 0) (aligned : incoming.toNat%8=0) (small : length.toNat≤64)
    (above : DeleteFrame.ceiling≤m.toNat) (before : m.toNat+16≤incoming.toNat) :
    Header target output.next m output.root flag := by
  have flagNumber : (m+8#64).toNat=m.toNat+8:=byteAddress_toNat m 8 (by have upper:=header.arena.upper; omega)
  have rootFrame:=output.older_word source target value m incoming length graph limit nodeLower pathLower property allowance
    frontier aligned small m header.rootSafe above (by omega)
  have flagFrame:=output.older_word source target value m incoming length graph limit nodeLower pathLower property allowance
    frontier aligned small (m+8#64) header.flagSafe (by rw [flagNumber]; omega) (by rw [flagNumber]; omega)
  have different : m+8#64≠m:=by intro equal; have numbers:=congrArg BitVec.toNat equal; omega
  exact ⟨header.arena,header.aligned,output.rootStored,(flagFrame.1 different).trans header.flagStored,
    output.rootMember,rootFrame.2,flagFrame.2⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.Output.older_word
#print axioms InitECandidate.Solver.Mpt.SetTrie.Header.after_set
