import InitECandidate.Solver.Mpt.TrieGraphRegister
import InitECandidate.Solver.Mpt.WitnessDecodeLeafView
import InitECandidate.Solver.Mpt.WitnessDecodeResult
import InitECandidate.Solver.Input.WitnessResolveResult
import InitECandidate.Solver.Mpt.WitnessCoreResolveState

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

def Registration.hashed (memory : Memory) (domain : BitVec 64 → Prop) (graph : Graph memory domain)
    (node : BitVec 64) (mapped : domain node) (stored : memory node=.word 0#64) : Registration graph node := by
  have tag : wordAt memory node=0#64 := by simp [wordAt,stored,MemoryBytes.wordBits]
  refine ⟨mapped,by rw [tag]; exact stored,?_,?_,?_,?_,by rw [tag]; decide⟩
  · intro pathTag
    have bad : False := by rw [tag] at pathTag; rcases pathTag with bad|bad <;> cases bad
    exact bad.elim
  · intro extensionTag; rw [tag] at extensionTag; cases extensionTag
  · intro extensionTag; rw [tag] at extensionTag; cases extensionTag
  · intro notHash; exact (notHash tag).elim

end InitECandidate.Solver.Mpt.TrieWalk

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

def LeafView.registration (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node db pointer length nibbles nibbleLength valuePointer valueLength : BitVec 64)
    (view : LeafView source node db pointer length nibbles nibbleLength valuePointer valueLength)
    (graph : TrieWalk.Graph source.memory source.memaddrs) : TrieWalk.Registration graph node := by
  have tag : wordAt source.memory node=1#64 := by simp [wordAt,view.tag,MemoryBytes.wordBits]
  refine ⟨?_,by rw [tag]; exact view.tag,fun _=>view.path,?_,?_,?_,by rw [tag]; decide⟩
  · simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source node 64 0 view.domain view.arena (by decide) view.aligned (by decide)
  · intro extensionTag; rw [tag] at extensionTag; cases extensionTag
  · intro extensionTag; rw [tag] at extensionTag; cases extensionTag
  · intro notHash notLeaf; exact (notLeaf tag).elim

noncomputable def LeafView.registered_values (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node db pointer length nibbles nibbleLength valuePointer valueLength : BitVec 64)
    (view : LeafView source node db pointer length nibbles nibbleLength valuePointer valueLength)
    (graph : TrieWalk.Graph source.memory source.memaddrs)
    (values : TrieWalk.Values graph 1024 (fun p n=>2713731432≤p.toNat ∧ p.toNat+n.toNat≤db.toNat)) :
    TrieWalk.Values (graph.register node (view.registration source node db pointer length nibbles nibbleLength valuePointer valueLength graph))
      1024 (fun p n=>2713731432≤p.toNat ∧ p.toNat+n.toNat≤db.toNat) := by
  have tag : wordAt source.memory node=1#64 := by simp [wordAt,view.tag,MemoryBytes.wordBits]
  exact TrieWalk.Values.register graph node (view.registration source node db pointer length nibbles nibbleLength valuePointer valueLength graph)
    1024 values (fun _=>view.value) (fun _ notLeaf _=>(notLeaf tag).elim)

/-- A genuine terminal decoder return supplies a completed null/leaf
registration from the actual leaf fields, rather than a future walk. -/
theorem terminal_registration (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit node : BitVec 64)
    (result : NormalResult post db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word node)]))
    (graph : TrieWalk.Graph post.memory post.memaddrs) :
    node=0#64 ∨ Nonempty (TrieWalk.Registration graph node) := by
  cases result with
  | empty scratch => exact Or.inl rfl
  | leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore =>
    exact Or.inr ⟨view.registration post node db pointer length nibbles nibbleLength valuePointer valueLength graph⟩

end InitECandidate.Solver.Mpt.WitnessDecode

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The genuine resolver terminal is null or a current physical hash node;
hash nodes need no path, value or child-closure hypotheses. -/
theorem resolve_terminal_registration (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap node : BitVec 64) (domain : post.memaddrs=InitE.ordinaryDomain) (aligned : heap.toNat%8=0)
    (result : ResolveResult post db heap (Mpt.WitnessCore.resolveAnswer 0#64 node 0#64 0#64))
    (graph : Mpt.TrieWalk.Graph post.memory post.memaddrs) :
    node=0#64 ∨ Nonempty (Mpt.TrieWalk.Registration graph node) := by
  rcases result with empty|⟨valueEq,arena,tag,hashData,finalHeap,actualCell,finalArena,finalAligned,before⟩|
      ⟨pointer,length,pending,valueEq,small,lower,upper,hashSpan⟩
  · exact Or.inl (by simpa [Mpt.WitnessCore.resolveAnswer] using empty)
  · have same : node=heap := by simpa [Mpt.WitnessCore.resolveAnswer] using valueEq
    subst node
    have mapped : post.memaddrs heap := by
      simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped post heap 32 0 domain arena (by decide) aligned (by decide)
    exact Or.inr ⟨Mpt.TrieWalk.Registration.hashed post.memory post.memaddrs graph heap mapped tag⟩
  · simp [Mpt.WitnessCore.resolveAnswer] at valueEq

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LeafView.registration
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LeafView.registered_values
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.terminal_registration
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.resolve_terminal_registration
