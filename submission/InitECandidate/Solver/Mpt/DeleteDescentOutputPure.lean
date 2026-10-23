import InitECandidate.Solver.Mpt.DeleteDescentOutput
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Package an actually derived terminal model through a real read-only
nonlocal frame. Caller locals and clock may change independently. -/
theorem DescentOutput.of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property)
    (next : DescentModel target key length limit nodeLower pathLower property)
    (heap : next.pending.heap=model.pending.heap) (cursor : next.pending.cursor=model.pending.cursor)
    (frame : next.pending.frame=model.pending.frame) (members : next.pending.graph.valid=model.pending.graph.valid)
    (stopped : next.go=0#64) (pureFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  have memory:=Input.LocalEffects.memory_of_erase source target pureFrame
  have globals:=congrArg PanSemStateFiniteExact.globals pureFrame
  change target.globals=source.globals at globals
  have fields:=TrieWalk.Graph.PathFields.of_agreement model.pending.graph target.memory (by intros; rw [memory])
  exact ⟨{
    next:=next
    grows:=by rw [heap]
    scratchDecreases:=by rw [cursor]
    frameEq:=frame
    members:=by intro node member; rw [members]; exact member
    freshMembers:=by intro node member; rw [members] at member; exact Or.inl member
    fields:=TrieWalk.Graph.PathFields.of_agreement model.pending.graph target.memory (by intros; rw [memory])
    memoryLow:=fun query _=>congrFun memory query
    memoryBand:=fun query _ _=>congrFun memory query
    protectedWords:=by
      intro address safe _above _before
      exact ⟨congrFun memory address,safe.of_fields model.pending.graph next.pending.graph address members fields⟩
    globals:=by intro name _ _; rw [globals]
    progress:=Or.inl stopped }⟩

/-- Exit a genuine auxiliary lexical scope without losing the real
descent outcome, including scratch, heap and current-key progress. -/
theorem DescentOutput.restore_auxiliary (source inner : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property)
    (name : String) (word : BitVec 64) (fresh : ofString name∉descentLocals)
    (output : DescentOutput (QueryBranch.bind source name word) inner key length limit nodeLower pathLower property
      (model.bind_auxiliary source key length limit nodeLower pathLower property name word fresh)) :
    Nonempty (DescentOutput source (QueryBranch.restore source name inner) key length limit nodeLower pathLower property model) :=
  ⟨{output with next:=output.next.restore_auxiliary source inner key length limit nodeLower pathLower property name fresh}⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.DescentOutput.of_erase
#print axioms InitECandidate.Solver.Mpt.DeleteBody.DescentOutput.restore_auxiliary
