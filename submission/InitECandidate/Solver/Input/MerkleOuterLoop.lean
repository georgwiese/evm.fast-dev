import InitECandidate.Solver.Input.MerkleOuterStep
import InitECandidate.Solver.Input.ClockCostPotentialLoop

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def outerTest : ExpHOL 64 := .cmp .less (.const 1#64) (localVar "cur")
def outerValid (cursor stp accel : BitVec 64) (capacity : Nat) (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ cur : Nat,1≤cur ∧ cur≤capacity ∧ state.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur))) ∧
    state.locals.lookup (ofString "buf")=some (.val (.word cursor)) ∧ ShaPair.Workspace state stp accel
def outerAllowance (state : PanSemStateFiniteExact 64 Guest.HostMemory) := 55*((CounterFlow.counterWord state (ofString "cur")).toNat-1)

theorem outer_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur : Nat) (small : cur<2^63)
    (current : source.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur)))) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) outerTest=
      some (.val (.word (if 1<cur then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 cur).toNat=cur := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have positiveSign : cur<9223372036854775808 := small
  simp [evalHOLFinite,evalHOLExact,toExact,outerTest,localVar,current,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,number,positiveSign]

/-- Actual dense Merkle hashing is linear in its starting leaf capacity.
The55*(cur-1) allowance pays actual shrinking pair loops and outer ticks,
including all aborted-body outcomes; no separate maximum is exponentiated. -/
theorem outer_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor stp accel : BitVec 64) (cur capacity : Nat)
    (positive : 1≤cur) (inside : cur≤capacity) (arena : AllocatedBytes.Arena cursor (32*capacity))
    (workspace : ShaPair.Workspace source stp accel)
    (current : source.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur))))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor))) :
    source.clock-(evaluateHOLFiniteState source outerLoop).2.clock≤55*(cur-1) := by
  classical
  have upper := arena.upper
  have step : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory,state.code=source.code → outerValid cursor stp accel capacity state → ∀ word,
      evalHOLFinite state (h:=fun address=>Classical.propDecidable (state.memaddrs address)) outerTest=some (.val (.word word)) → word≠0 → state.clock≠0 →
      let output := evaluateHOLFiniteState (decClockHOLFinite state) outerStep
      state.clock-output.2.clock≤outerAllowance state ∧
      ((output.1=none ∨ output.1=some .continue) → outerValid cursor stp accel capacity output.2 ∧
        state.clock-output.2.clock+outerAllowance output.2≤outerAllowance state) := by
    intro state codeEq valid word read nonzero funded
    obtain ⟨count,countPositive,countBound,countCell,bufferCell,currentWorkspace⟩ := valid
    have small : count<2^63 := by omega
    have number : (BitVec.ofNat 64 count).toNat=count := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have expected := outer_test_read state count small countCell
    have active : 1<count := by
      by_contra inactive
      rw [if_neg inactive] at expected
      have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero zero
    have allowance : outerAllowance state=55*(count-1) := by simp [outerAllowance,CounterFlow.counterWord,countCell,valueWord,number]
    let output := evaluateHOLFiniteState (decClockHOLFinite state) outerStep
    have entryWorkspace := ShaPair.Workspace.of_fields state (decClockHOLFinite state) stp accel currentWorkspace rfl rfl rfl rfl
    have bodyCost := outer_step_cost (decClockHOLFinite state) cursor stp accel count capacity countBound arena entryWorkspace countCell bufferCell
    have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) outerStep
    change state.clock-1-output.2.clock≤54*(count/2) at bodyCost
    change output.2.clock≤state.clock-1 at bodyClock
    have spent : state.clock-output.2.clock≤54*(count/2)+1 := by omega
    have paid := halving_budget count active
    have stopped : state.clock-output.2.clock≤outerAllowance state := by rw [allowance]; omega
    refine ⟨stopped,?_⟩
    intro continuing
    have summary := (outer_other (ofString "buf") (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite state)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite state) outerStep=(none,output.2) := Prod.ext normal rfl
    have nextCur := outer_advances (decClockHOLFinite state) output.2 count (by omega) countCell run
    have nextBuffer := (summary.1 normal).trans bufferCell
    have nextWorkspace := outer_workspace (decClockHOLFinite state) output.2 stp accel entryWorkspace none run
    have nextNumber : (BitVec.ofNat 64 (count/2)).toNat=count/2 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have nextAllowance : outerAllowance output.2=55*(count/2-1) := by simp only [outerAllowance,CounterFlow.counterWord,nextCur,Option.getD_some,valueWord,nextNumber]
    have continuedPaid : state.clock-output.2.clock+outerAllowance output.2≤outerAllowance state := by
      rw [nextAllowance,allowance]
      omega
    exact ⟨⟨count/2,by omega,by omega,nextCur,nextBuffer,nextWorkspace⟩,continuedPaid⟩
  have cost := ClockCost.potential_loop source.code outerTest outerStep (outerValid cursor stp accel capacity) outerAllowance step source rfl
    ⟨cur,positive,inside,current,buffer,workspace⟩
  have number : (BitVec.ofNat 64 cur).toNat=cur := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [outer_shape.1]
  simpa only [outerTest,outerAllowance,CounterFlow.counterWord,current,Option.getD_some,valueWord,number] using cost

theorem outer_loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code outerLoop := by
  rw [outer_shape.1]
  exact GlobalEffects.loop key code _ _ (outer_globals key code installed)

theorem outer_loop_other (key : MlS) (notCur : key≠ofString "cur") (notHalf : key≠ofString "half") (notJ : key≠ofString "j") :
    LocalPrefix key outerLoop := by
  rw [outer_shape.1]
  exact LocalPrefix.loop _ (outer_other key notCur notHalf notJ)

theorem outer_loop_workspace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel : BitVec 64)
    (workspace : ShaPair.Workspace source stp accel) (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source outerLoop=(result,post)) :
    ShaPair.Workspace post stp accel :=
  ShaPair.Workspace.after source post stp accel workspace outerLoop result run
    (outer_loop_globals (ofString "sha_st") source.code workspace.installed) (outer_loop_globals (ofString "sha_accel") source.code workspace.installed)

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.outer_test_read
#print axioms InitECandidate.Solver.Input.Merkle.outer_loop_cost
#print axioms InitECandidate.Solver.Input.Merkle.outer_loop_globals
#print axioms InitECandidate.Solver.Input.Merkle.outer_loop_other
#print axioms InitECandidate.Solver.Input.Merkle.outer_loop_workspace
