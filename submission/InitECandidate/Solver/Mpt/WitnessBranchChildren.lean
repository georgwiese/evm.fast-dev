import InitECandidate.Solver.Mpt.TrieGraphRegister
import InitECandidate.Solver.Mpt.WitnessCoreBranchPrefix

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Exactly the already returned child slots of an active branch.
Unvisited slots need no initialized-memory or future-resolution premise. -/
def Children (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop)
    (node : BitVec 64) (count : Nat) : Prop :=
  ∀ index<count,∃ child,source.memory (byteAddress node (32+8*index))=.word child ∧ valid child

theorem Children.empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop) (node : BitVec 64) :
    Children source valid node 0 := by intro index inside; omega

theorem Children.frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (valid : BitVec 64 → Prop) (node : BitVec 64) (count : Nat) (children : Children source valid node count)
    (agree : ∀ index<count,target.memory (byteAddress node (32+8*index))=source.memory (byteAddress node (32+8*index))) :
    Children target valid node count := by
  intro index inside
  obtain ⟨child,stored,member⟩ := children index inside
  exact ⟨child,(agree index inside).trans stored,member⟩

theorem Children.enlarge (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : BitVec 64 → Prop) (node : BitVec 64) (count : Nat) (children : Children source first node count)
    (includes : ∀ child,first child → second child) : Children source second node count := by
  intro index inside
  obtain ⟨child,stored,member⟩ := children index inside
  exact ⟨child,stored,includes child member⟩

theorem Children.store_next (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (valid : BitVec 64 → Prop) (node child : BitVec 64) (index : Fin 16)
    (children : Children source valid node index.val) (member : valid child) :
    Children {source with memory:=StoreWord.put source.memory (WitnessRecord.childAddress node index) child} valid node (index.val+1) := by
  intro current inside
  by_cases same : current=index.val
  · subst current
    exact ⟨child,if_pos rfl,member⟩
  · have before : current<index.val := by omega
    obtain ⟨oldChild,stored,oldMember⟩ := children current before
    have away : byteAddress node (32+8*current)≠WitnessRecord.childAddress node index := by
      intro equal
      have cancelled : BitVec.ofNat 64 (32+8*current)=BitVec.ofNat 64 (32+8*index.val) :=
        (BitVec.add_right_inj node).mp equal
      have number := congrArg BitVec.toNat cancelled
      rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bound:=index.isLt; omega),Nat.mod_eq_of_lt (by have bound:=index.isLt; omega)] at number
      omega
    exact ⟨oldChild,(if_neg away).trans stored,oldMember⟩

/-- The actual child/OCC/i prefix retains every completed child,
including the just written current slot. Scratch OCC is below the node. -/
theorem Children.counter_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (valid : BitVec 64 → Prop) (record node child : BitVec 64) (index : Fin 16) (occupied : Fin 17)
    (children : Children source valid node index.val) (member : valid child)
    (nodeArena : AllocatedBytes.Arena node 176) (floor : 2713731432≤node.toNat) (ceiling : record.toNat+88≤2713717616) :
    Children (branchCounterEntry source record node child index occupied) valid node (index.val+1) := by
  let written : PanSemStateFiniteExact 64 Guest.HostMemory := {source with memory:=StoreWord.put source.memory (WitnessRecord.childAddress node index) child}
  have next := children.store_next source valid node child index member
  apply next.frame written (branchCounterEntry source record node child index occupied) valid node (index.val+1)
  intro current inside
  have currentBound : current<16 := by have bound:=index.isLt; omega
  have number : (byteAddress node (32+8*current)).toNat=node.toNat+(32+8*current) := byteAddress_toNat node _ (by have upper:=nodeArena.upper; omega)
  have recordNumber : (record+40#64).toNat=record.toNat+40 := byteAddress_toNat record 40 (by omega)
  have away : byteAddress node (32+8*current)≠record+40#64 := by
    intro equal; have same:=congrArg BitVec.toNat equal; rw [number,recordNumber] at same; omega
  by_cases zero : child=0#64 <;> simp [branchCounterEntry,occupancyState,zero,QueryBranch.bind,setVarHOLFinite,StoreWord.put,written,away]

/-- Once all sixteen actual child stores have completed, their physical
closed pointers provide precisely the branch part of the walk registry. -/
noncomputable def Children.registration (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (node : BitVec 64)
    (children : Children source graph.valid node 16) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena node 176) (aligned : node.toNat%8=0) (stored : source.memory node=.word 3#64) :
    TrieWalk.Registration graph node := by
  have tag : wordAt source.memory node=3#64 := by simp [wordAt,stored,MemoryBytes.wordBits]
  refine ⟨?_,by rw [tag]; exact stored,?_,?_,?_,?_,by rw [tag]; decide⟩
  · simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source node 176 0 domain arena (by decide) aligned (by decide)
  · intro pathTag
    have bad : False := by rw [tag] at pathTag; rcases pathTag with bad|bad <;> cases bad
    exact bad.elim
  · intro extensionTag; rw [tag] at extensionTag; cases extensionTag
  · intro extensionTag; rw [tag] at extensionTag; cases extensionTag
  · intro notHash notLeaf notExtension index inside
    let child:=Classical.choose (children index inside)
    have actual:=Classical.choose_spec (children index inside)
    have addressEq : byteAddress node (32+8*index)=node+32#64+BitVec.ofNat 64 (index*8) := by
      rw [byteAddress,BitVec.ofNat_add,←BitVec.add_assoc,Nat.mul_comm 8 index]
    exact ⟨child,by rw [←addressEq]; exact AllocatedBytes.word_mapped source node 176 (32+8*index) domain arena (by omega) aligned (by omega),
      by rw [←addressEq]; exact actual.1,actual.2⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Children.store_next
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Children.counter_entry
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Children.registration
