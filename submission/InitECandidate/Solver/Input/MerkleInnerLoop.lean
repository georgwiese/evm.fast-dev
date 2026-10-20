import InitECandidate.Solver.Input.MerkleInnerProgram
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def innerTest : ExpHOL 64 := .cmp .less (localVar "j") (localVar "half")
def innerValid (cursor stp accel : BitVec 64) (half : Nat) (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ index : Nat,index≤half ∧ state.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))) ∧
    state.locals.lookup (ofString "half")=some (.val (.word (BitVec.ofNat 64 half))) ∧
    state.locals.lookup (ofString "buf")=some (.val (.word cursor)) ∧ ShaPair.Workspace state stp accel
def innerRank (half : Nat) (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat := half-(CounterFlow.counterWord state (ofString "j")).toNat

theorem inner_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index half : Nat)
    (small : half<2^63) (inside : index≤half)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))))
    (h : source.locals.lookup (ofString "half")=some (.val (.word (BitVec.ofNat 64 half)))) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) innerTest=
      some (.val (.word (if index<half then 1#64 else 0#64))) := by
  have jNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hNumber : (BitVec.ofNat 64 half).toNat=half := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have indexSmall : index<9223372036854775808 := by omega
  have halfSmall : half<9223372036854775808 := small
  simp [evalHOLFinite,evalHOLExact,toExact,innerTest,localVar,j,h,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,jNumber,hNumber,indexSmall,halfSmall]

private theorem inner_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index half : Nat)
    (small : half<2^63) (inside : index≤half)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))))
    (h : source.locals.lookup (ofString "half")=some (.val (.word (BitVec.ofNat 64 half)))) (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) innerTest=some (.val (.word word))) (nonzero : word≠0) : index<half := by
  have expected := inner_test_read source index half small inside j h
  by_contra inactive
  rw [if_neg inactive] at expected
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

/-- All original dense pair-loop outcomes cost at most54 ticks per actual
remaining pair. Continuing iterations derive current mapped operands and the
next workspace/counter from their real body execution. -/
theorem inner_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor stp accel : BitVec 64) (index half : Nat)
    (small : half<2^63) (inside : index≤half) (arena : AllocatedBytes.Arena cursor (64*half))
    (workspace : ShaPair.Workspace source stp accel)
    (j : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))))
    (h : source.locals.lookup (ofString "half")=some (.val (.word (BitVec.ofNat 64 half))))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor))) :
    source.clock-(evaluateHOLFiniteState source innerLoop).2.clock≤54*(half-index) := by
  classical
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → innerValid cursor stp accel half current → ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) innerTest=some (.val (.word word)) → word≠0 → current.clock≠0 →
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) innerStep).2.clock≤53 := by
    intro current codeEq valid word read nonzero funded
    obtain ⟨position,bounded,currentJ,currentHalf,currentBuffer,currentWorkspace⟩ := valid
    have active := inner_active current position half small bounded currentJ currentHalf word read nonzero
    have entryWorkspace := ShaPair.Workspace.of_fields current (decClockHOLFinite current) stp accel currentWorkspace rfl rfl rfl rfl
    exact inner_step_cost (decClockHOLFinite current) cursor stp accel position half entryWorkspace active arena currentBuffer currentJ
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → innerValid cursor stp accel half current → ∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) innerTest=some (.val (.word word)) → word≠0 →
      0<innerRank half current ∧ (current.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite current) innerStep
        (output.1=none ∨ output.1=some .continue) → innerValid cursor stp accel half output.2 ∧ innerRank half output.2<innerRank half current) := by
    intro current codeEq valid word read nonzero
    obtain ⟨position,bounded,currentJ,currentHalf,currentBuffer,currentWorkspace⟩ := valid
    have active := inner_active current position half small bounded currentJ currentHalf word read nonzero
    have number : (BitVec.ofNat 64 position).toNat=position := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have rankEq : innerRank half current=half-position := by simp [innerRank,CounterFlow.counterWord,currentJ,valueWord,number]
    refine ⟨by rw [rankEq]; omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output := evaluateHOLFiniteState (decClockHOLFinite current) innerStep
    have summary := (inner_other (ofString "half") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite current) innerStep=(none,output.2) := Prod.ext normal rfl
    have nextJ : output.2.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 (position+1)))) := by
      have advanced := inner_advances (decClockHOLFinite current) output.2 (BitVec.ofNat 64 position) currentJ run
      simpa only [BitVec.ofNat_add] using advanced
    have nextHalf := (summary.1 normal).trans currentHalf
    have bufferSummary := (inner_other (ofString "buf") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at bufferSummary
    have nextBuffer := (bufferSummary.1 normal).trans currentBuffer
    have entryWorkspace := ShaPair.Workspace.of_fields current (decClockHOLFinite current) stp accel currentWorkspace rfl rfl rfl rfl
    have nextWorkspace := ShaPair.Workspace.after (decClockHOLFinite current) output.2 stp accel entryWorkspace innerStep none run
      (inner_globals (ofString "sha_st") _ entryWorkspace.installed) (inner_globals (ofString "sha_accel") _ entryWorkspace.installed)
    have nextNumber : (BitVec.ofNat 64 (position+1)).toNat=position+1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have nextRank : innerRank half output.2=half-(position+1) := by simp only [innerRank,CounterFlow.counterWord,nextJ,Option.getD_some,valueWord,nextNumber]
    exact ⟨⟨position+1,by omega,nextJ,nextHalf,nextBuffer,nextWorkspace⟩,by rw [nextRank,rankEq]; omega⟩
  have cost := ClockCost.ranked_loop_current source.code innerTest innerStep 53 (innerValid cursor stp accel half) (innerRank half) priced progress source rfl
    ⟨index,inside,j,h,buffer,workspace⟩
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [inner_shape.1]
  simpa only [innerTest,innerRank,CounterFlow.counterWord,j,Option.getD_some,valueWord,number] using cost

theorem inner_loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code innerLoop := by
  rw [inner_shape.1]
  exact GlobalEffects.loop key code _ _ (inner_globals key code installed)

theorem inner_loop_other (key : MlS) (different : key≠ofString "j") : LocalPrefix key innerLoop := by
  rw [inner_shape.1]
  exact LocalPrefix.loop _ (inner_other key different)

theorem inner_loop_workspace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel : BitVec 64)
    (workspace : ShaPair.Workspace source stp accel) (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source innerLoop=(result,post)) :
    ShaPair.Workspace post stp accel :=
  ShaPair.Workspace.after source post stp accel workspace innerLoop result run
    (inner_loop_globals (ofString "sha_st") source.code workspace.installed) (inner_loop_globals (ofString "sha_accel") source.code workspace.installed)

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.inner_test_read
#print axioms InitECandidate.Solver.Input.Merkle.inner_loop_cost
#print axioms InitECandidate.Solver.Input.Merkle.inner_loop_globals
#print axioms InitECandidate.Solver.Input.Merkle.inner_loop_other
#print axioms InitECandidate.Solver.Input.Merkle.inner_loop_workspace
