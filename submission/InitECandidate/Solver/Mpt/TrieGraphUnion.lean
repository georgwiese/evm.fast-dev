import InitECandidate.Solver.Mpt.TrieGraphRegisteredRegions

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget

def ChildView.map_valid {memory : Memory} {domain : BitVec 64 → Prop}
    {valid next : BitVec 64 → Prop} {address : BitVec 64}
    (view : ChildView memory domain valid address) (inclusion : ∀ node,valid node → next node) : ChildView memory domain next address:=
  ⟨view.child,view.mapped,view.stored,inclusion _ view.member⟩

/-- Join two physically closed graphs in the same current memory.
Children remain in the corresponding old graph and hence in the union. -/
noncomputable def Graph.union {memory : Memory} {domain : BitVec 64 → Prop}
    (first second : Graph memory domain) : Graph memory domain := by
  classical
  let valid:=fun node=>first.valid node ∨ second.valid node
  have extension : ∀ node,valid node → node≠0#64 → wordAt memory node=2#64 → ChildView memory domain valid (node+48#64):=by
    intro node member active tag
    by_cases old : first.valid node
    · exact (first.extension node old active tag).map_valid (fun _ h=>Or.inl h)
    · exact (second.extension node (member.resolve_left old) active tag).map_valid (fun _ h=>Or.inr h)
  refine {valid:=valid,null:=Or.inl first.null,header:=?_,path:=?_,extension:=extension,zeroHop:=?_,branch:=?_}
  · intro node member active
    rcases member with left|right
    · exact first.header node left active
    · exact second.header node right active
  · intro node member active tag
    by_cases old : first.valid node
    · exact first.path node old active tag
    · exact second.path node (member.resolve_left old) active tag
  · intro node member active tag zero
    change (extension node member active tag).child=0#64 ∨ wordAt memory (extension node member active tag).child≠2#64
    rcases member with left|right
    · have same : (extension node (Or.inl left) active tag).child=(first.extension node left active tag).child:=
        HolWordLab.word.inj ((extension node (Or.inl left) active tag).stored.symm.trans (first.extension node left active tag).stored)
      rw [same]; exact first.zeroHop node left active tag zero
    · have same : (extension node (Or.inr right) active tag).child=(second.extension node right active tag).child:=
        HolWordLab.word.inj ((extension node (Or.inr right) active tag).stored.symm.trans (second.extension node right active tag).stored)
      rw [same]; exact second.zeroHop node right active tag zero
  · intro node member active notHash notLeaf notExtension index inside
    by_cases old : first.valid node
    · exact (first.branch node old active notHash notLeaf notExtension index inside).map_valid (fun _ h=>Or.inl h)
    · exact (second.branch node (member.resolve_left old) active notHash notLeaf notExtension index inside).map_valid (fun _ h=>Or.inr h)

noncomputable def Values.union {memory : Memory} {domain : BitVec 64 → Prop}
    (first second : Graph memory domain) (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (left : Values first limit property) (right : Values second limit property) : Values (first.union second) limit property := by
  classical
  constructor
  · intro node member active tag
    by_cases old : first.valid node
    · exact left.leaf node old active tag
    · exact right.leaf node (member.resolve_left old) active tag
  · intro node member active notHash notLeaf notExtension
    by_cases old : first.valid node
    · exact left.branch node old active notHash notLeaf notExtension
    · exact right.branch node (member.resolve_left old) active notHash notLeaf notExtension

theorem Graph.Regions.union {memory : Memory} {domain : BitVec 64 → Prop}
    (first second : Graph memory domain) (lower middle upper : Nat)
    (left : first.Regions lower middle) (right : second.Regions middle upper) (ordered : lower≤middle) (grows : middle≤upper) :
    (first.union second).Regions lower upper := by
  intro node member active
  rcases member with old|fresh
  · exact left.weaken first lower middle lower upper (Nat.le_refl _) grows node old active
  · exact right.weaken second middle upper lower upper ordered (Nat.le_refl _) node fresh active

/-- Disjoint allocation intervals on opposite sides of the actual heap
frontier remain disjoint when their closed node graphs are joined. -/
theorem Graph.Disjoint.union {memory : Memory} {domain : BitVec 64 → Prop}
    (first second : Graph memory domain) (lower middle upper : Nat)
    (leftRegions : first.Regions lower middle) (rightRegions : second.Regions middle upper)
    (left : first.Disjoint) (right : second.Disjoint) : (first.union second).Disjoint := by
  intro a memberA activeA b memberB activeB different
  rcases memberA with oldA|freshA
  · rcases memberB with oldB|freshB
    · exact left a oldA activeA b oldB activeB different
    · exact Or.inl ((leftRegions a oldA activeA).2.2.2.trans (rightRegions b freshB activeB).1)
  · rcases memberB with oldB|freshB
    · exact Or.inr ((leftRegions b oldB activeB).2.2.2.trans (rightRegions a freshA activeA).1)
    · exact right a freshA activeA b freshB activeB different

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.union
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Values.union
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Regions.union
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Disjoint.union
