import InitECandidate.Solver.Headers.ValidateRound
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def incremented (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) := bind source "i" (BitVec.ofNat 64 (index+1))

theorem increment_round (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) :
    evaluateHOLFiniteState source increment=(none,incremented source index) ∧ RoundState data origin (incremented source index) (index+1) := by
  have read : eval source (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,state.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have actual:=WitnessRadix.StateSteps.assign_execute source "i" (.op .add [localVar "i",.const 1#64]) (BitVec.ofNat 64 index) (BitVec.ofNat 64 (index+1)) state.indexCell read
  have frame : Input.HashInput.Frame source (incremented source index) data.lower data.upper := ⟨by intro query lower upper; rfl⟩
  have nextArena:=Rlp.Validation.Arena.of_fields source (incremented source index) data.cursor data.limit state.arena rfl rfl
  have nextEnvironment:=Keccak256.Environment.of_fields source (incremented source index) data.stp data.pad state.environment rfl rfl rfl (by intro key other; rfl)
  refine ⟨actual,state.installed,state.shape,nextArena,nextEnvironment,state.input.trans origin source _ _ _ frame,
    state.rows.of_frame source _ _ _ _ _ _ _ frame,state.heap,?_,?_,?_,?_,?_,state.globals⟩
  · exact (bind_lookup_other source "i" "arr" _ (by decide)).trans state.arrayCell
  · exact (bind_lookup_other source "i" "n" _ (by decide)).trans state.countCell
  · exact (bind_lookup_other source "i" "hs" _ (by decide)).trans state.hsCell
  · exact (bind_lookup_other source "i" "hashes" _ (by decide)).trans state.hashesCell
  · exact bind_lookup_same source "i" _

/-- Both actual per-row scopes restore only their own temporary binding;
the counter advanced by their genuine continuation remains current. -/
theorem RoundState.restore_temporary (data : Data) (origin saved source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (name : String) (temporary : name="h" ∨ name="eq") :
    RoundState data origin (restore saved name source) index := by
  let target:=restore saved name source
  have frame : Input.HashInput.Frame source target data.lower data.upper := ⟨by intro query lower upper; rfl⟩
  have nextArena:=Rlp.Validation.Arena.of_fields source target data.cursor data.limit state.arena rfl rfl
  have nextEnvironment:=Keccak256.Environment.of_fields source target data.stp data.pad state.environment rfl rfl rfl (by intro key other; rfl)
  refine ⟨state.installed,state.shape,nextArena,nextEnvironment,state.input.trans origin source target _ _ frame,
    state.rows.of_frame source target _ _ _ _ _ _ frame,state.heap,?_,?_,?_,?_,?_,state.globals⟩
  · exact (restore_lookup_other saved source name "arr" (by rcases temporary with rfl|rfl <;> decide)).trans state.arrayCell
  · exact (restore_lookup_other saved source name "n" (by rcases temporary with rfl|rfl <;> decide)).trans state.countCell
  · exact (restore_lookup_other saved source name "hs" (by rcases temporary with rfl|rfl <;> decide)).trans state.hsCell
  · exact (restore_lookup_other saved source name "hashes" (by rcases temporary with rfl|rfl <;> decide)).trans state.hashesCell
  · exact (restore_lookup_other saved source name "i" (by rcases temporary with rfl|rfl <;> decide)).trans state.indexCell

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.increment_round
#print axioms InitECandidate.Solver.Headers.Validate.RoundState.restore_temporary
