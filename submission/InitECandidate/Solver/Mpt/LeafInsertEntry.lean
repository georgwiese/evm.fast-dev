import InitECandidate.Solver.Mpt.LeafInsertDispatch
import InitECandidate.Solver.Mpt.TrieWalkRead
import InitECandidate.Solver.Mpt.TrieWalkMemory
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def fieldEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64):=
  bind (bind source "ek" (wordAt source.memory (node+32#64))) "el" (wordAt source.memory (node+40#64))

theorem field_entry_lookup_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (name : MlS)
    (notKey : name≠ofString "ek") (notLength : name≠ofString "el") :
    (fieldEntry source node).locals.lookup name=source.locals.lookup name := by
  simp [fieldEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm notKey,Ne.symm notLength]

theorem field_entry_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) :
    (fieldEntry source node).locals.lookup (ofString "ek")=some (.val (.word (wordAt source.memory (node+32#64)))) ∧
    (fieldEntry source node).locals.lookup (ofString "el")=some (.val (.word (wordAt source.memory (node+40#64)))) := by
  simp [fieldEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

/-- Read the original leaf's actual path fields and reach its genuine
comparison/split continuation. The graph supplies the mapped real words;
successful future comparison, splitting or allocation is not assumed. -/
theorem field_entry_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (node : BitVec 64)
    (member : graph.valid node) (active : node≠0#64) (leaf : wordAt source.memory node=1#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ inner,evaluateHOLFiniteState (fieldEntry source node) afterLength=(some (.returned value),inner) ∧
      post=restore source "ek" (restore (bind source "ek" (wordAt source.memory (node+32#64))) "el" inner) := by
  let path:=graph.path node member active (Or.inl leaf)
  have keyStored : source.memory (node+32#64)=.word (wordAt source.memory (node+32#64)):=by
    simp only [wordAt,path.pointerStored,MemoryBytes.wordBits]
  have lengthStored : source.memory (node+40#64)=.word (wordAt source.memory (node+40#64)):=by
    simp only [wordAt,path.sizeStored,MemoryBytes.wordBits]
  have keyRead : eval source keyExpression=some (.val (.word (wordAt source.memory (node+32#64)))):=by
    simpa only [keyExpression,TrieWalk.nodeField] using TrieWalk.node_field_read source node 32#64 (wordAt source.memory (node+32#64)) nodeCell path.pointerMapped keyStored
  rw [dispatch_shapes.1] at normal
  obtain ⟨middle,keyRun,endpoint⟩:=Input.declaration_return_word source post "ek" keyExpression (wordAt source.memory (node+32#64)) afterKey value keyRead normal
  let keyed:=bind source "ek" (wordAt source.memory (node+32#64))
  have currentNode : keyed.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other source "ek" "node" _ (by decide)).trans nodeCell
  have lengthRead : eval keyed lengthExpression=some (.val (.word (wordAt source.memory (node+40#64)))):=by
    simpa only [lengthExpression,TrieWalk.nodeField] using TrieWalk.node_field_read keyed node 40#64 (wordAt source.memory (node+40#64)) currentNode path.sizeMapped lengthStored
  rw [dispatch_shapes.2.1] at keyRun
  obtain ⟨inner,lengthRun,lengthEndpoint⟩:=Input.declaration_return_word keyed middle "el" lengthExpression (wordAt source.memory (node+40#64)) afterLength value lengthRead keyRun
  exact ⟨inner,lengthRun,by rw [endpoint,lengthEndpoint]⟩

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.field_entry_lookup_other
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.field_entry_cells
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.field_entry_normal
