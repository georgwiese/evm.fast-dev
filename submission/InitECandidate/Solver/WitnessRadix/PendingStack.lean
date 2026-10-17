import InitECandidate.Solver.WitnessRadix.PopStoreFrame

namespace InitECandidate.Solver.WitnessRadix.PendingStack
open Flapjack PanSemStateFiniteExact

structure Task where
  start : Nat
  input : List (BitVec 64)
  parent : BitVec 64
  parentPosition : Nat

def Represents {F : Type} (source : PanSemStateFiniteExact 64 F)
    (pendingStart pendingCount pendingNode : BitVec 64) : List Task → Prop
  | [] => True
  | task :: rest =>
      PopProgram.Cells source (BitVec.ofNat 64 (rest.length + 1)) pendingStart pendingCount pendingNode
        (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 task.input.length) task.parent (BitVec.ofNat 64 task.parentPosition) ∧
      Represents source pendingStart pendingCount pendingNode rest

def reads (pendingStart pendingCount pendingNode : BitVec 64) : List Task → BitVec 64 → Prop
  | [], _ => False
  | task :: rest, query =>
      query = pendingStart + (BitVec.ofNat 64 (rest.length + 1) - 1#64) * 8#64 ∨
      query = pendingCount + (BitVec.ofNat 64 (rest.length + 1) - 1#64) * 8#64 ∨
      query = pendingNode + (BitVec.ofNat 64 (rest.length + 1) - 1#64) * 8#64 ∨
      query = task.parent ∨ reads pendingStart pendingCount pendingNode rest query

theorem head_cells {F : Type} (source : PanSemStateFiniteExact 64 F)
    (pendingStart pendingCount pendingNode : BitVec 64) (task : Task) (rest : List Task)
    (rep : Represents source pendingStart pendingCount pendingNode (task :: rest)) :
    PopProgram.Cells source (BitVec.ofNat 64 (task :: rest).length) pendingStart pendingCount pendingNode
      (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 task.input.length) task.parent (BitVec.ofNat 64 task.parentPosition) := by
  simpa only [List.length_cons] using rep.1

/-- All suffix and saved-parent reads survive arbitrary other writes. -/
theorem represents_of_agreement {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (domain : source.memaddrs = target.memaddrs) (pendingStart pendingCount pendingNode : BitVec 64) (tasks : List Task)
    (agree : ∀ query, reads pendingStart pendingCount pendingNode tasks query → source.memory query = target.memory query)
    (rep : Represents source pendingStart pendingCount pendingNode tasks) :
    Represents target pendingStart pendingCount pendingNode tasks := by
  induction tasks with
  | nil => trivial
  | cons task rest ih =>
      obtain ⟨cells, tail⟩ := rep
      rcases cells with ⟨a,b,c,d,e,f,g,h⟩
      rw [domain] at a c e g
      refine ⟨⟨a, (agree _ (Or.inl rfl)).symm.trans b,
        c, (agree _ (Or.inr (Or.inl rfl))).symm.trans d,
        e, (agree _ (Or.inr (Or.inr (Or.inl rfl)))).symm.trans f,
        g, (agree _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).symm.trans h⟩, ?_⟩
      exact ih (fun query member => agree query (Or.inr (Or.inr (Or.inr (Or.inr member))))) tail

/-- Popping a task changes only locals, so all remaining suffix cells and
parent bits keep their exact representation. -/
theorem pop_tail {F : Type} (source : PanSemStateFiniteExact 64 F)
    (pendingStart pendingCount pendingNode : BitVec 64) (task : Task) (rest : List Task)
    (rep : Represents source pendingStart pendingCount pendingNode (task :: rest)) :
    Represents (PopProgram.popPost source (BitVec.ofNat 64 (task :: rest).length)
      (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 task.input.length) task.parent (BitVec.ofNat 64 task.parentPosition))
      pendingStart pendingCount pendingNode rest := by
  exact represents_of_agreement source
    (PopProgram.popPost source (BitVec.ofNat 64 (task :: rest).length)
      (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 task.input.length) task.parent (BitVec.ofNat 64 task.parentPosition))
    rfl _ _ _ rest (by intros; rfl) rep.2

end InitECandidate.Solver.WitnessRadix.PendingStack

#print axioms InitECandidate.Solver.WitnessRadix.PendingStack.head_cells
#print axioms InitECandidate.Solver.WitnessRadix.PendingStack.represents_of_agreement
#print axioms InitECandidate.Solver.WitnessRadix.PendingStack.pop_tail
