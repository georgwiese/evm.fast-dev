import InitECandidate.Solver.Mpt.DeleteFrameStack
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget

/-- Actual parent facts retained by a saved extension/branch activation.
An extension stores its genuine complete path fields; a branch stores a
genuine bounded nibble index. Children may change during unwinding. -/
def Saved.Owned {memory : Memory} {domain : BitVec 64→Prop} (saved : Saved) (graph : TrieWalk.Graph memory domain) : Prop:=
  graph.valid saved.node ∧ saved.node≠0#64 ∧ wordAt memory saved.node=saved.kind.tag ∧
    match saved.kind with
    | .extension=>wordAt memory (saved.node+32#64)=saved.words "seg" ∧ wordAt memory (saved.node+40#64)=saved.words "sl"
    | .branch=>(saved.words "idx").toNat<16

/-- A real parent remains valid through a mutation that retains old
members, initialized tags and the stored path fields. Fresh nodes are
permitted, and no edge order or path-content equality is presumed. -/
theorem Saved.Owned.of_fields {memory memory' : Memory} {domain domain' : BitVec 64→Prop}
    (saved : Saved) (graph : TrieWalk.Graph memory domain) (next : TrieWalk.Graph memory' domain')
    (owned : saved.Owned graph) (members : ∀ node,graph.valid node→next.valid node)
    (fields : graph.PathFields memory') : saved.Owned next := by
  obtain ⟨member,active,tag,data⟩:=owned
  refine ⟨members saved.node member,active,(fields.tags saved.node member active).trans tag,?_⟩
  cases kindEq : saved.kind with
  | branch=>simpa only [kindEq] using data
  | extension=>
    have pathTag : wordAt memory saved.node=2#64:=by simpa only [kindEq,Kind.tag] using tag
    have words:=fields.fields saved.node member active (Or.inr pathTag)
    simpa only [kindEq,words.1,words.2] using data

def Parents {memory : Memory} {domain : BitVec 64→Prop} (graph : TrieWalk.Graph memory domain) (frames : List Saved) : Prop:=
  ∀ saved∈frames,saved.Owned graph

theorem Parents.of_fields {memory memory' : Memory} {domain domain' : BitVec 64→Prop}
    (graph : TrieWalk.Graph memory domain) (next : TrieWalk.Graph memory' domain') (frames : List Saved)
    (parents : Parents graph frames) (members : ∀ node,graph.valid node→next.valid node)
    (fields : graph.PathFields memory') : Parents next frames := by
  intro saved member
  exact (parents saved member).of_fields saved graph next members fields

theorem Parents.push {memory : Memory} {domain : BitVec 64→Prop}
    (graph : TrieWalk.Graph memory domain) (frames : List Saved) (parents : Parents graph frames)
    (saved : Saved) (owned : saved.Owned graph) : Parents graph (saved::frames) := by
  intro current member
  rcases List.mem_cons.mp member with same|older
  · subst current; exact owned
  · exact parents current older

theorem Parents.pop {memory : Memory} {domain : BitVec 64→Prop}
    (graph : TrieWalk.Graph memory domain) (saved : Saved) (frames : List Saved)
    (parents : Parents graph (saved::frames)) : saved.Owned graph ∧ Parents graph frames :=
  ⟨parents saved (by simp),fun current member=>parents current (List.mem_cons_of_mem saved member)⟩

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Saved.Owned.of_fields
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Parents.of_fields
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Parents.push
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Parents.pop
