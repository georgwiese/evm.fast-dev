import InitECandidate.Solver.Mpt.DeleteDescentPure
import InitECandidate.Solver.Mpt.DeleteDescentOutput
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real null-node terminal choice assigns res0 and stops after the
original iteration has cleared go. All physical caller memory survives. -/
theorem null_node_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property)
    (null : model.node=0#64) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source nodeChoice=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  have chosen : evaluateHOLFiniteState source nodeChoice=evaluateHOLFiniteState source (.assign .local (ofString "res") (.const 0#64)):=by
    rw [descent_shapes.2.2.1,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,model.nodeCell,null,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have actual:=assign_result_execute source key length limit nodeLower pathLower property model (.const 0#64) 0#64 rfl
  have endpoint : target=QueryBranch.bind source "res" 0#64:=congrArg Prod.snd (normal.symm.trans (chosen.trans actual))
  rw [endpoint]
  let next:=model.bind_result source key length limit nodeLower pathLower property 0#64 model.pending.graph.null
  exact ⟨{
    next:=next
    grows:=Nat.le_refl _
    scratchDecreases:=Nat.le_refl _
    frameEq:=rfl
    members:=fun _ member=>member
    freshMembers:=fun _ member=>Or.inl member
    fields:=TrieWalk.Graph.PathFields.of_agreement model.pending.graph source.memory (fun _ _=>rfl)
    memoryLow:=fun _ _=>rfl
    memoryBand:=fun _ _ _=>rfl
    globals:=fun _ _ _=>rfl
    progress:=Or.inl stopped }⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.null_node_output
