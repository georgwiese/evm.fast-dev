import InitECandidate.Solver.Mpt.TrieGraphPathFields

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A real child-word replacement preserves closure. Every selected
child slot now contains the registered replacement; all other slots retain
their original child. Positive extension paths exclude zero-hop loops. -/
noncomputable def Graph.of_child_word (memory : Memory) (domain : BitVec 64 → Prop) (graph : Graph memory domain)
    (be : Bool) (paths : graph.PathBytes be) (address child : BitVec 64) (childMember : graph.valid child)
    (headers : ∀ node,graph.valid node → node≠0#64 → StoreWord.put memory address child node=memory node)
    (pathWords : ∀ node,graph.valid node → node≠0#64 → (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
      StoreWord.put memory address child (node+32#64)=memory (node+32#64) ∧
      StoreWord.put memory address child (node+40#64)=memory (node+40#64)) :
    Graph (StoreWord.put memory address child) domain := by
  classical
  let nextMemory:=StoreWord.put memory address child
  have tags : ∀ node,graph.valid node → node≠0#64 → wordAt nextMemory node=wordAt memory node:=by
    intro node member active
    change MemoryBytes.wordBits (StoreWord.put memory address child node)=MemoryBytes.wordBits (memory node)
    rw [headers node member active]
  have childView (slot : BitVec 64) (old : ChildView memory domain graph.valid slot) : ChildView nextMemory domain graph.valid slot:=by
    by_cases same : slot=address
    · exact ⟨child,old.mapped,by simp [nextMemory,same,StoreWord.put],childMember⟩
    · exact ⟨old.child,old.mapped,by change StoreWord.put memory address child slot=.word old.child; rw [StoreWord.put,if_neg same]; exact old.stored,old.member⟩
  refine {valid:=graph.valid,null:=graph.null,header:=?_,path:=?_,extension:=?_,zeroHop:=?_,branch:=?_,kindBound:=?_}
  · intro node member active
    obtain ⟨mapped,stored⟩:=graph.header node member active
    exact ⟨mapped,by rw [headers node member active,tags node member active]; exact stored⟩
  · intro node member active tag
    have oldTag : wordAt memory node=1#64 ∨ wordAt memory node=2#64:=by rwa [tags node member active] at tag
    let old:=graph.path node member active oldTag
    have same:=pathWords node member active oldTag
    exact {
      size:=old.size
      pointer:=old.pointer
      sizeMapped:=old.sizeMapped
      sizeStored:=same.2.trans old.sizeStored
      pointerMapped:=old.pointerMapped
      pointerStored:=same.1.trans old.pointerStored
      fits:=old.fits
      mapped:=old.mapped }
  · intro node member active tag
    have oldTag : wordAt memory node=2#64:=by rwa [tags node member active] at tag
    exact childView _ (graph.extension node member active oldTag)
  · intro node member active tag zero
    have oldTag : wordAt memory node=2#64:=by rwa [tags node member active] at tag
    have sizeEq : wordAt nextMemory (node+40#64)=wordAt memory (node+40#64):=by
      change MemoryBytes.wordBits (StoreWord.put memory address child (node+40#64))=MemoryBytes.wordBits (memory (node+40#64))
      rw [(pathWords node member active (Or.inr oldTag)).2]
    have empty : wordAt memory (node+40#64)=0#64:=sizeEq.symm.trans zero
    have positive:=paths.positive node member active oldTag
    rw [empty] at positive
    exact (by simp at positive)
  · intro node member active notHash notLeaf notExtension index inside
    rw [tags node member active] at notHash notLeaf notExtension
    exact childView _ (graph.branch node member active notHash notLeaf notExtension index inside)

  · intro node member active
    rw [tags node member active]
    exact graph.kindBound node member active

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.of_child_word
