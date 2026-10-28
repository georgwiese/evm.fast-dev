import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context
import InitECandidate.Solver.Input.CurrentTable.NewContext

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- An empty tree needs no initialized node-array cells. -/
theorem empty_nodes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    Nodes source base (fun _=>False) (fun _=>256) (fun _=>0#64) (fun _=>0#64) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> intro node impossible <;> exact False.elim impossible

/-- Establish the traversal image and mapped header from the actual
returned current constructor. This is the empty base of the required
insertion invariant, rather than a supplied successful lookup hypothesis. -/
theorem empty_from_constructor {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap stp pad : BitVec 64}
    (returned : New.Returned source post table cap stp pad) :
    Context post table (New.nodesPointer table cap) 0#64 (fun _=>False) (fun _=>256) (fun _=>0#64) (fun _=>0#64) := by
  have keyCell : post.memory table=.word 32#64 := by
    simpa only [BitVec.add_zero] using returned.fields (table+0#64,32#64) (by simp [New.writes])
  have nodesCell : post.memory (table+40#64)=.word (New.nodesPointer table cap) :=
    returned.fields (table+40#64,New.nodesPointer table cap) (by simp [New.writes])
  have rootCell : post.memory (table+56#64)=.word 0#64 :=
    returned.fields (table+56#64,0#64) (by simp [New.writes])
  exact ⟨empty_nodes post _,Or.inl rfl,returned.arena.domain,returned.geometry.table,returned.tableAligned,keyCell,nodesCell,rootCell⟩

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.empty_nodes
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.empty_from_constructor
