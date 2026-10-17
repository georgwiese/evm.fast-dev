import InitECandidate.Solver.WitnessRadix.QueryFootprint

namespace InitECandidate.Solver.WitnessRadix.OpenGraph
open Flapjack PanSemStateFiniteExact

/-- A construction frontier. Every subtree owns its incoming pointer slot;
holes carry the mathematical tree still to be built at that slot. -/
inductive Tree where
  | hole (slot : BitVec 64) (expected : Graph.Tree)
  | complete (slot root : BitVec 64) (tree : Graph.Tree)
  | branch (slot node : BitVec 64) (position : Nat) (zero one : Tree)

def slot : Tree → BitVec 64
  | .hole address _ => address
  | .complete address _ _ => address
  | .branch address _ _ _ _ => address

def expected : Tree → Graph.Tree
  | .hole _ tree => tree
  | .complete _ _ tree => tree
  | .branch _ _ position zero one => .branch position (expected zero) (expected one)

def frontier : Tree → List (BitVec 64 × Graph.Tree)
  | .hole address tree => [(address, tree)]
  | .complete _ _ _ => []
  | .branch _ _ _ zero one => frontier zero ++ frontier one

def Represents {F : Type} (source : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64) : Tree → Prop
  | .hole address _ => source.memaddrs address
  | .complete address root tree =>
      source.memaddrs address ∧ source.memory address = .word root ∧
      QueryMemory.Represents source table keys vals root tree
  | .branch address node position zero one =>
      source.memaddrs address ∧ source.memory address = .word node ∧
      node ≠ 0#64 ∧ node &&& 1#64 = 0#64 ∧ position < 256 ∧
      source.memaddrs node ∧ source.memory node = .word (BitVec.ofNat 64 position) ∧
      slot zero = node + 8#64 ∧ slot one = node + 16#64 ∧
      Represents source table keys vals zero ∧ Represents source table keys vals one

def reads {F : Type} (source : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64) : Tree → BitVec 64 → Prop
  | .hole _ _, _ => False
  | .complete address root tree, query => query = address ∨ QueryMemory.reads source table keys vals root tree query
  | .branch address node _ zero one, query =>
      query = address ∨ query = node ∨ reads source table keys vals zero query ∨ reads source table keys vals one query

theorem slot_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64)
    (tree : Tree) (rep : Represents source table keys vals tree) : source.memaddrs (slot tree) := by
  cases tree with
  | hole address tree => exact rep
  | complete address root tree => exact rep.1
  | branch address node position zero one => exact rep.1

/-- Once no frontier remains, the actual memory satisfies precisely the
representation consumed by the complete lookup theorem. -/
theorem completed {F : Type} (source : PanSemStateFiniteExact 64 F) (table keys vals : BitVec 64)
    (tree : Tree) (rep : Represents source table keys vals tree) (closed : frontier tree = []) :
    ∃ root : BitVec 64, source.memaddrs (slot tree) ∧ source.memory (slot tree) = .word root ∧
      QueryMemory.Represents source table keys vals root (expected tree) := by
  induction tree with
  | hole address tree => simp [frontier] at closed
  | complete address root tree => exact ⟨root, rep⟩
  | branch address node position zero one ihZero ihOne =>
      rcases rep with ⟨mapped, word, nonzero, even, inside, nodeMapped, nodeWord, zeroSlot, oneSlot, zeroRep, oneRep⟩
      have zeroClosed : frontier zero = [] := (List.append_eq_nil_iff.mp closed).1
      have oneClosed : frontier one = [] := (List.append_eq_nil_iff.mp closed).2
      obtain ⟨zeroRoot, zeroMapped, zeroWord, zeroTree⟩ := ihZero zeroRep zeroClosed
      obtain ⟨oneRoot, oneMapped, oneWord, oneTree⟩ := ihOne oneRep oneClosed
      rw [zeroSlot] at zeroMapped zeroWord
      rw [oneSlot] at oneMapped oneWord
      exact ⟨node, mapped, word, nonzero, even, inside, nodeMapped, nodeWord, zeroMapped, oneMapped,
        zeroRoot, oneRoot, zeroWord, oneWord, zeroTree, oneTree⟩

/-- All established edges/subtrees survive writes away from their concrete
read footprint; holes demand mapping but no existing pointer value. -/
theorem represents_of_agreement {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (table keys vals : BitVec 64) (tree : Tree)
    (agree : ∀ query, reads source table keys vals tree query → source.memory query = target.memory query)
    (rep : Represents source table keys vals tree) : Represents target table keys vals tree := by
  induction tree with
  | hole address tree => change target.memaddrs address; rw [← domain]; exact rep
  | complete address root tree =>
      exact ⟨by rw [← domain]; exact rep.1,
        (agree _ (Or.inl rfl)).symm.trans rep.2.1,
        QueryMemory.represents_of_agreement source target domain endian table keys vals root tree
          (fun query member => agree query (Or.inr member)) rep.2.2⟩
  | branch address node position zero one ihZero ihOne =>
      rcases rep with ⟨mapped, word, nonzero, even, inside, nodeMapped, nodeWord, zeroSlot, oneSlot, zeroRep, oneRep⟩
      rw [domain] at mapped nodeMapped
      exact ⟨mapped, (agree _ (Or.inl rfl)).symm.trans word, nonzero, even, inside, nodeMapped,
        (agree _ (Or.inr (Or.inl rfl))).symm.trans nodeWord, zeroSlot, oneSlot,
        ihZero (fun query member => agree query (Or.inr (Or.inr (Or.inl member)))) zeroRep,
        ihOne (fun query member => agree query (Or.inr (Or.inr (Or.inr member)))) oneRep⟩

end InitECandidate.Solver.WitnessRadix.OpenGraph

#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.completed
#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.represents_of_agreement
