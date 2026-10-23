import InitECandidate.Solver.Mpt.SplitExtensionProgram
import InitECandidate.Solver.Mpt.TrieWalkRead
import InitECandidate.Solver.Mpt.TrieWalkMemory
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def fieldEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64):=
  bind (bind (bind source "seg" (wordAt source.memory (node+32#64))) "sl" (wordAt source.memory (node+40#64))) "child" (wordAt source.memory (node+48#64))

theorem field_entry_lookup_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (name : MlS)
    (notSegment : name≠ofString "seg") (notLength : name≠ofString "sl") (notChild : name≠ofString "child") :
    (fieldEntry source node).locals.lookup name=source.locals.lookup name := by
  simp [fieldEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm notSegment,Ne.symm notLength,Ne.symm notChild]

theorem field_entry_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) :
    (fieldEntry source node).locals.lookup (ofString "seg")=some (.val (.word (wordAt source.memory (node+32#64)))) ∧
    (fieldEntry source node).locals.lookup (ofString "sl")=some (.val (.word (wordAt source.memory (node+40#64)))) ∧
    (fieldEntry source node).locals.lookup (ofString "child")=some (.val (.word (wordAt source.memory (node+48#64)))) := by
  simp [fieldEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

theorem stored_child_member (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (node : BitVec 64) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=2#64) : graph.valid (wordAt source.memory (node+48#64)) := by
  let view:=graph.extension node member active tag
  have childWord : wordAt source.memory (node+48#64)=view.child:=by simp only [wordAt,view.stored,MemoryBytes.wordBits]
  rw [childWord]
  exact view.member

/-- The actual original250 entry loads the real mapped extension path
and child fields, reaching its genuine branch allocation scope. -/
theorem field_entry_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (node : BitVec 64)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ inner,evaluateHOLFiniteState (fieldEntry source node) branchScope=(some (.returned value),inner) ∧
      post=restore source "seg" (restore (bind source "seg" (wordAt source.memory (node+32#64))) "sl"
        (restore (bind (bind source "seg" (wordAt source.memory (node+32#64))) "sl" (wordAt source.memory (node+40#64))) "child" inner)) := by
  let path:=graph.path node member active (Or.inr tag)
  let child:=graph.extension node member active tag
  have keyStored : source.memory (node+32#64)=.word (wordAt source.memory (node+32#64)):=by simp only [wordAt,path.pointerStored,MemoryBytes.wordBits]
  have lengthStored : source.memory (node+40#64)=.word (wordAt source.memory (node+40#64)):=by simp only [wordAt,path.sizeStored,MemoryBytes.wordBits]
  have childStored : source.memory (node+48#64)=.word (wordAt source.memory (node+48#64)):=by simp only [wordAt,child.stored,MemoryBytes.wordBits]
  have keyRead : eval source (fieldExpression 32#64)=some (.val (.word (wordAt source.memory (node+32#64)))):=by
    simpa only [fieldExpression,TrieWalk.nodeField] using TrieWalk.node_field_read source node 32#64 _ nodeCell path.pointerMapped keyStored
  rw [entry_shapes.1] at normal
  obtain ⟨first,keyRun,endpoint⟩:=Input.declaration_return_word source post "seg" (fieldExpression 32#64) (wordAt source.memory (node+32#64)) afterSegment value keyRead normal
  let keyed:=bind source "seg" (wordAt source.memory (node+32#64))
  have keyedNode : keyed.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other source "seg" "node" _ (by decide)).trans nodeCell
  have lengthRead : eval keyed (fieldExpression 40#64)=some (.val (.word (wordAt source.memory (node+40#64)))):=by
    simpa only [fieldExpression,TrieWalk.nodeField] using TrieWalk.node_field_read keyed node 40#64 _ keyedNode path.sizeMapped lengthStored
  rw [entry_shapes.2.1] at keyRun
  obtain ⟨second,lengthRun,lengthEndpoint⟩:=Input.declaration_return_word keyed first "sl" (fieldExpression 40#64) (wordAt source.memory (node+40#64)) afterLength value lengthRead keyRun
  let lengthed:=bind keyed "sl" (wordAt source.memory (node+40#64))
  have currentNode : lengthed.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other keyed "sl" "node" _ (by decide)).trans keyedNode
  have childRead : eval lengthed (fieldExpression 48#64)=some (.val (.word (wordAt source.memory (node+48#64)))):=by
    simpa only [fieldExpression,TrieWalk.nodeField] using TrieWalk.node_field_read lengthed node 48#64 _ currentNode child.mapped childStored
  rw [entry_shapes.2.2.1] at lengthRun
  obtain ⟨inner,childRun,childEndpoint⟩:=Input.declaration_return_word lengthed second "child" (fieldExpression 48#64) (wordAt source.memory (node+48#64)) branchScope value childRead lengthRun
  exact ⟨inner,childRun,by rw [endpoint,lengthEndpoint,childEndpoint]⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.field_entry_lookup_other
#print axioms InitECandidate.Solver.Mpt.SplitExtension.field_entry_cells
#print axioms InitECandidate.Solver.Mpt.SplitExtension.stored_child_member
#print axioms InitECandidate.Solver.Mpt.SplitExtension.field_entry_normal
