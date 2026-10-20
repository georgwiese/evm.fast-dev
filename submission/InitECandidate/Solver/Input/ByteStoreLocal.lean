import InitECandidate.Solver.Input.SharedStoreLocal
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix.QueryBranch

/-- Actual ordinary byte stores retain every current caller binding on
continuation and cannot escape as return, break or continue. -/
theorem byte_store_local {F : Type} (key : MlS) (address value : ExpHOL 64) (source : PanSemStateFiniteExact 64 F) :
    LocalSummary key (.storeByte address value) source := by
  unfold LocalSummary
  rw [evaluateHOLFiniteState_storeByte]
  repeat' first | split | simp

/-- A normal ordinary byte store advances no current caller counter. -/
theorem CounterFlow.byte_store (key : MlS) (address value : ExpHOL 64) : Advances key 0 (.storeByte address value) := by
  intro source post word cell run
  have summary := byte_store_local key address value source
  unfold LocalSummary at summary
  rw [run] at summary
  simpa only [BitVec.add_zero] using (summary.1 rfl).trans cell

/-- Actual local counter increments by a fixed source-word amount. -/
theorem CounterFlow.increment_by (key : MlS) (amount : Nat) :
    Advances key amount (.assign .local key (.op .add [.var .local key,.const (BitVec.ofNat 64 amount)])) := by
  intro source post word cell run
  have read : eval source (.op .add [.var .local key,.const (BitVec.ofNat 64 amount)])=some (.val (.word (word+BitVec.ofNat 64 amount))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,cell,valueIsWord,valueWord,wordOpHOL,wordOp]
  simp only [eval] at read
  rw [evaluateHOLFiniteState_assign,read] at run
  have valid : isValidValueHOLFinite source .local key (.val (.word (word+BitVec.ofNat 64 amount)))=true := by
    simp [isValidValueHOLFinite,lookupKvarHOLFinite,cell,shapeOfHOLExact,shapeEqHOL]
  simp only [←isValidValueHOLFinite_eq,valid,if_pos,setKvarHOLFinite] at run
  have postEq := congrArg Prod.snd run
  change setVarHOLFinite key (.val (.word (word+BitVec.ofNat 64 amount))) source=post at postEq
  rw [←postEq]
  simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.byte_store_local
#print axioms InitECandidate.Solver.Input.CounterFlow.byte_store
#print axioms InitECandidate.Solver.Input.CounterFlow.increment_by
