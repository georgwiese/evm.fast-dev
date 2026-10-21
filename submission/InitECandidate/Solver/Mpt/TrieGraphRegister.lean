import InitECandidate.Solver.Mpt.TrieWalkValues

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget

/-- Physical fields of one completed node. Its children already belong
to the current registry; this does not assume a future walk or allocation. -/
structure Registration {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (node : BitVec 64) where
  mapped : domain node
  header : memory node = .word (wordAt memory node)
  path : (wordAt memory node=1#64 ∨ wordAt memory node=2#64) → PathView memory domain node
  extension : wordAt memory node=2#64 → ChildView memory domain graph.valid (node+48#64)
  zeroHop : ∀ tag : wordAt memory node=2#64, wordAt memory (node+40#64)=0#64 →
    (extension tag).child=0#64 ∨ wordAt memory (extension tag).child≠2#64
  branch : wordAt memory node≠0#64 → wordAt memory node≠1#64 → wordAt memory node≠2#64 →
    ∀ index, index<16 → ChildView memory domain graph.valid (node+32#64+BitVec.ofNat 64 (index*8))

private def ChildView.enlarge {memory : Memory} {domain : BitVec 64 → Prop}
    {valid : BitVec 64 → Prop} {address : BitVec 64} (view : ChildView memory domain valid address) (node : BitVec 64) :
    ChildView memory domain (fun pointer=>valid pointer ∨ pointer=node) address :=
  ⟨view.child,view.mapped,view.stored,Or.inl view.member⟩

private theorem ChildView.unique {memory : Memory} {domain : BitVec 64 → Prop}
    {first second : BitVec 64 → Prop} {address : BitVec 64}
    (left : ChildView memory domain first address) (right : ChildView memory domain second address) : left.child=right.child :=
  HolWordLab.word.inj (left.stored.symm.trans right.stored)

/-- Add a node using its actual initialized physical fields. -/
noncomputable def Graph.register {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (node : BitVec 64) (data : Registration graph node) : Graph memory domain := by
  classical
  let valid := fun pointer=>graph.valid pointer ∨ pointer=node
  have extension : ∀ current,valid current → current≠0#64 → wordAt memory current=2#64 →
      ChildView memory domain valid (current+48#64) := by
    intro current member active tag
    by_cases old : graph.valid current
    · exact (graph.extension current old active tag).enlarge node
    · have fresh := member.resolve_left old
      subst current
      exact (data.extension tag).enlarge node
  refine { valid:=valid, null:=Or.inl graph.null, header:=?_, path:=?_, extension:=extension, zeroHop:=?_, branch:=?_ }
  · intro current member active
    rcases member with old|fresh
    · exact graph.header current old active
    · subst current; exact ⟨data.mapped,data.header⟩
  · intro current member active tag
    by_cases old : graph.valid current
    · exact graph.path current old active tag
    · have fresh := member.resolve_left old
      subst current; exact data.path tag
  · intro current member active tag zero
    rcases member with old|fresh
    · have same := ChildView.unique (extension current (Or.inl old) active tag) (graph.extension current old active tag)
      change (extension current (Or.inl old) active tag).child=0#64 ∨ wordAt memory (extension current (Or.inl old) active tag).child≠2#64
      rw [same]
      exact graph.zeroHop current old active tag zero
    · subst current
      have same := ChildView.unique (extension node (Or.inr rfl) active tag) (data.extension tag)
      change (extension node (Or.inr rfl) active tag).child=0#64 ∨ wordAt memory (extension node (Or.inr rfl) active tag).child≠2#64
      rw [same]
      exact data.zeroHop tag zero
  · intro current member active notHash notLeaf notExtension index inside
    by_cases old : graph.valid current
    · exact (graph.branch current old active notHash notLeaf notExtension index inside).enlarge node
    · have fresh := member.resolve_left old
      subst current; exact (data.branch notHash notLeaf notExtension index inside).enlarge node

theorem Graph.register_valid {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (node : BitVec 64) (data : Registration graph node) :
    (graph.register node data).valid = (fun pointer=>graph.valid pointer ∨ pointer=node) := rfl

noncomputable def Values.register {memory : Memory} {domain : BitVec 64 → Prop}
    {property : BitVec 64 → BitVec 64 → Prop} (graph : Graph memory domain) (node : BitVec 64)
    (data : Registration graph node) (limit : Nat) (values : Values graph limit property)
    (leaf : wordAt memory node=1#64 → ValueView memory domain node 48#64 56#64 limit property)
    (branch : wordAt memory node≠0#64 → wordAt memory node≠1#64 → wordAt memory node≠2#64 →
      ValueView memory domain node 160#64 168#64 limit property) : Values (graph.register node data) limit property := by
  classical
  constructor
  · intro current member active tag
    by_cases old : graph.valid current
    · exact values.leaf current old active tag
    · have fresh := member.resolve_left old
      subst current; exact leaf tag
  · intro current member active notHash notLeaf notExtension
    by_cases old : graph.valid current
    · exact values.branch current old active notHash notLeaf notExtension
    · have fresh := member.resolve_left old
      subst current; exact branch notHash notLeaf notExtension

/-- The actual empty completed-node registry before materialization. -/
def Graph.empty (memory : Memory) (domain : BitVec 64 → Prop) : Graph memory domain := by
  refine { valid:=fun node=>node=0#64, null:=rfl, header:=?_, path:=?_, extension:=?_, zeroHop:=?_, branch:=?_ }
  all_goals intro node member active; exact (active member).elim

def Values.empty (memory : Memory) (domain : BitVec 64 → Prop) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) : Values (Graph.empty memory domain) limit property := by
  constructor
  all_goals intro node member active; exact (active member).elim

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.register
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Values.register
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.empty
