import InitECandidate.Solver.Input.MerkleExtensionProgram
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def extensionValid (cursor zeros stp accel : BitVec 64) (target : Nat) (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ index : Nat,index≤target ∧ state.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))) ∧
    state.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))) ∧
    state.locals.lookup (ofString "buf")=some (.val (.word cursor)) ∧
    state.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)) ∧ ShaPair.Workspace state stp accel
def extensionRank (target : Nat) (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat := target-(CounterFlow.counterWord state (ofString "d")).toNat

theorem extension_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index target : Nat)
    (small : target<64) (inside : index≤target)
    (d : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))))
    (t : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target)))) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) extensionTest=
      some (.val (.word (if index<target then 1#64 else 0#64))) := by
  have dNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have tNumber : (BitVec.ofNat 64 target).toNat=target := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have indexSmall : index<9223372036854775808 := by omega
  have targetSmall : target<9223372036854775808 := by omega
  simp [evalHOLFinite,evalHOLExact,toExact,extensionTest,localVar,d,t,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,dNumber,tNumber,indexSmall,targetSmall]

private theorem extension_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index target : Nat)
    (small : target<64) (inside : index≤target)
    (d : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))))
    (t : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target)))) (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) extensionTest=some (.val (.word word))) (nonzero : word≠0) : index<target := by
  have expected := extension_test_read source index target small inside d t
  by_contra inactive
  rw [if_neg inactive] at expected
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

/-- Extension hashes cost54 per actual remaining tree depth. Every current
pair operand is mapped from the real root/zero-hash arenas, and the real
continuing execution supplies its next counter and workspace. -/
theorem extension_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor zeros stp accel : BitVec 64) (index target : Nat)
    (small : target<64) (inside : index≤target) (bufferArena : AllocatedBytes.Arena cursor 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (workspace : ShaPair.Workspace source stp accel)
    (d : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))))
    (t : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros))) :
    source.clock-(evaluateHOLFiniteState source extensionLoop).2.clock≤54*(target-index) := by
  classical
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → extensionValid cursor zeros stp accel target current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) extensionTest=some (.val (.word word)) → word≠0 → current.clock≠0 →
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) extensionStep).2.clock≤53 := by
    intro current codeEq valid word read nonzero funded
    obtain ⟨position,bounded,currentD,currentTarget,currentBuffer,currentTable,currentWorkspace⟩ := valid
    have active := extension_active current position target small bounded currentD currentTarget word read nonzero
    have entryWorkspace := ShaPair.Workspace.of_fields current (decClockHOLFinite current) stp accel currentWorkspace rfl rfl rfl rfl
    exact extension_step_cost (decClockHOLFinite current) cursor zeros stp accel position (by omega) entryWorkspace bufferArena tableArena currentBuffer currentD currentTable
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → extensionValid cursor zeros stp accel target current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) extensionTest=some (.val (.word word)) → word≠0 →
      0<extensionRank target current ∧ (current.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite current) extensionStep
        (output.1=none ∨ output.1=some .continue) → extensionValid cursor zeros stp accel target output.2 ∧ extensionRank target output.2<extensionRank target current) := by
    intro current codeEq valid word read nonzero
    obtain ⟨position,bounded,currentD,currentTarget,currentBuffer,currentTable,currentWorkspace⟩ := valid
    have active := extension_active current position target small bounded currentD currentTarget word read nonzero
    have number : (BitVec.ofNat 64 position).toNat=position := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have rankEq : extensionRank target current=target-position := by simp [extensionRank,CounterFlow.counterWord,currentD,valueWord,number]
    refine ⟨by rw [rankEq]; omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output := evaluateHOLFiniteState (decClockHOLFinite current) extensionStep
    have summary := (extension_other (ofString "target") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite current) extensionStep=(none,output.2) := Prod.ext normal rfl
    have nextD : output.2.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 (position+1)))) := by
      have advanced := extension_advances (decClockHOLFinite current) output.2 (BitVec.ofNat 64 position) currentD run
      simpa only [BitVec.ofNat_add] using advanced
    have nextTarget := (summary.1 normal).trans currentTarget
    have bufferSummary := (extension_other (ofString "buf") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at bufferSummary
    have nextBuffer := (bufferSummary.1 normal).trans currentBuffer
    have entryWorkspace := ShaPair.Workspace.of_fields current (decClockHOLFinite current) stp accel currentWorkspace rfl rfl rfl rfl
    have tableFrame := extension_globals (ofString "zero_hashes") (decClockHOLFinite current).code entryWorkspace.installed (decClockHOLFinite current) rfl
    rw [run] at tableFrame
    have nextTable : output.2.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)) := (congrArg Prod.snd tableFrame).trans currentTable
    have nextWorkspace := ShaPair.Workspace.after (decClockHOLFinite current) output.2 stp accel entryWorkspace extensionStep none run
      (extension_globals (ofString "sha_st") _ entryWorkspace.installed) (extension_globals (ofString "sha_accel") _ entryWorkspace.installed)
    have nextNumber : (BitVec.ofNat 64 (position+1)).toNat=position+1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have nextRank : extensionRank target output.2=target-(position+1) := by simp only [extensionRank,CounterFlow.counterWord,nextD,Option.getD_some,valueWord,nextNumber]
    exact ⟨⟨position+1,by omega,nextD,nextTarget,nextBuffer,nextTable,nextWorkspace⟩,by rw [nextRank,rankEq]; omega⟩
  have cost := ClockCost.ranked_loop_current source.code extensionTest extensionStep 53 (extensionValid cursor zeros stp accel target) (extensionRank target) priced progress source rfl
    ⟨index,inside,d,t,buffer,table,workspace⟩
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [extension_shape.2.1]
  simpa only [extensionRank,CounterFlow.counterWord,d,Option.getD_some,valueWord,number] using cost

theorem extension_loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code extensionLoop := by
  rw [extension_shape.2.1]
  exact GlobalEffects.loop key code _ _ (extension_globals key code installed)

theorem extension_loop_other (key : MlS) (different : key≠ofString "d") : LocalPrefix key extensionLoop := by
  rw [extension_shape.2.1]
  exact LocalPrefix.loop _ (extension_other key different)

theorem extension_loop_workspace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel : BitVec 64)
    (workspace : ShaPair.Workspace source stp accel) (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source extensionLoop=(result,post)) :
    ShaPair.Workspace post stp accel :=
  ShaPair.Workspace.after source post stp accel workspace extensionLoop result run
    (extension_loop_globals (ofString "sha_st") source.code workspace.installed) (extension_loop_globals (ofString "sha_accel") source.code workspace.installed)

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.extension_test_read
#print axioms InitECandidate.Solver.Input.Merkle.extension_loop_cost
#print axioms InitECandidate.Solver.Input.Merkle.extension_loop_globals
#print axioms InitECandidate.Solver.Input.Merkle.extension_loop_other
#print axioms InitECandidate.Solver.Input.Merkle.extension_loop_workspace
