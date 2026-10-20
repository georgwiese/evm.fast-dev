import InitECandidate.Solver.Input.ProgressiveFoldProgram
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem fold_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots acc : BitVec 64) (k : Nat)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k)))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) foldArguments=
      some (ShaPair.values (roots+BitVec.ofNat 64 (32*k)) acc acc) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,foldArguments,localVar,root,accumulator,round,ShaPair.values,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

theorem fold_step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots acc stp accel : BitVec 64) (k : Nat)
    (positive : 0<k) (inside : k≤15) (workspace : ShaPair.Workspace source stp accel)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k))))
    (rootsArena : AllocatedBytes.Arena roots 768) (accArena : AllocatedBytes.Arena acc 32) :
    source.clock-(evaluateHOLFiniteState source foldStep).2.clock≤53 := by
  let entry := bind source "k" (BitVec.ofNat 64 (k-1))
  have assigned := StateSteps.assign_execute source "k" decrementExpression (BitVec.ofNat 64 k) (BitVec.ofNat 64 (k-1)) round (decrement_read source k positive (by omega) round)
  have args := fold_arguments entry roots acc (k-1)
    ((bind_lookup_other source "k" "roots" (BitVec.ofNat 64 (k-1)) (by decide)).trans root)
    ((bind_lookup_other source "k" "acc" (BitVec.ofNat 64 (k-1)) (by decide)).trans accumulator) (bind_lookup_same _ _ _)
  have inputArena := AllocatedBytes.Arena.subrange roots 768 (32*(k-1)) 32 rootsArena (by omega)
  have pairCost := ShaPair.call_cost entry (roots+BitVec.ofNat 64 (32*(k-1))) acc acc stp accel workspace.installed (some none) foldArguments args
    workspace.state workspace.accelerator workspace.domain inputArena accArena workspace.arena workspace.aligned
  rw [fold_shape.2.1,StateSteps.next_sequence source entry decrement _ assigned (Nat.le_refl _)]
  exact pairCost

def foldValid (roots acc stp accel : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ k : Nat,k≤15 ∧ source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k))) ∧
    source.locals.lookup (ofString "roots")=some (.val (.word roots)) ∧ source.locals.lookup (ofString "acc")=some (.val (.word acc)) ∧ ShaPair.Workspace source stp accel

def foldRank (source : PanSemStateFiniteExact 64 Guest.HostMemory) := (CounterFlow.counterWord source (ofString "k")).toNat

theorem fold_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) (inside : k≤15)
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k)))) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) foldTest=
      some (.val (.word (if k=0 then 0#64 else 1#64))) := by
  have number : (BitVec.ofNat 64 k).toNat=k := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have zero : (BitVec.ofNat 64 k=0#64) ↔ k=0 := by
    constructor
    · intro same; have h:=congrArg BitVec.toNat same; simpa only [number,BitVec.toNat_ofNat] using h
    · intro same; subst k; rfl
  simp [evalHOLFinite,evalHOLExact,toExact,foldTest,localVar,round,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]

private theorem fold_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) (inside : k≤15)
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k)))) (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) foldTest=some (.val (.word word))) (nonzero : word≠0) : 0<k := by
  have expected := fold_test_read source k inside round
  by_contra inactive
  have zero : k=0 := by omega
  rw [if_pos zero] at expected
  have wordZero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero wordZero

/-- The original final root fold costs54 ticks per actual saved root,
including arbitrary pair/FFI failures and every other loop outcome. -/
theorem fold_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots acc stp accel : BitVec 64) (k : Nat)
    (inside : k≤15) (workspace : ShaPair.Workspace source stp accel)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 k))))
    (rootsArena : AllocatedBytes.Arena roots 768) (accArena : AllocatedBytes.Arena acc 32) :
    source.clock-(evaluateHOLFiniteState source foldLoop).2.clock≤54*k := by
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → foldValid roots acc stp accel current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) foldTest=some (.val (.word word)) → word≠0 → current.clock≠0 →
      current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) foldStep).2.clock≤53 := by
    intro current codeEq valid word read nonzero funded
    obtain ⟨position,bounded,currentK,currentRoots,currentAcc,currentWorkspace⟩ := valid
    have active := fold_active current position bounded currentK word read nonzero
    exact fold_step_cost (decClockHOLFinite current) roots acc stp accel position active bounded
      (ShaPair.Workspace.of_fields current _ stp accel currentWorkspace rfl rfl rfl rfl) currentRoots currentAcc currentK rootsArena accArena
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → foldValid roots acc stp accel current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) foldTest=some (.val (.word word)) → word≠0 →
      0<foldRank current ∧ (current.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite current) foldStep
        (output.1=none ∨ output.1=some .continue) → foldValid roots acc stp accel output.2 ∧ foldRank output.2<foldRank current) := by
    intro current codeEq valid word read nonzero
    obtain ⟨position,bounded,currentK,currentRoots,currentAcc,currentWorkspace⟩ := valid
    have active := fold_active current position bounded currentK word read nonzero
    have number : (BitVec.ofNat 64 position).toNat=position := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have rankEq : foldRank current=position := by simp [foldRank,CounterFlow.counterWord,currentK,valueWord,number]
    refine ⟨by rw [rankEq]; exact active,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output := evaluateHOLFiniteState (decClockHOLFinite current) foldStep
    have summary := (fold_other (ofString "roots") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have run : evaluateHOLFiniteState (decClockHOLFinite current) foldStep=(none,output.2) := Prod.ext normal rfl
    have nextK := fold_advances (decClockHOLFinite current) output.2 position active (by omega) currentK run
    have nextRoots := (summary.1 normal).trans currentRoots
    have accSummary := (fold_other (ofString "acc") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at accSummary
    have nextAcc := (accSummary.1 normal).trans currentAcc
    have entryWorkspace := ShaPair.Workspace.of_fields current (decClockHOLFinite current) stp accel currentWorkspace rfl rfl rfl rfl
    have nextWorkspace := ShaPair.Workspace.after (decClockHOLFinite current) output.2 stp accel entryWorkspace foldStep none run
      (fold_globals (ofString "sha_st") current.code currentWorkspace.installed) (fold_globals (ofString "sha_accel") current.code currentWorkspace.installed)
    have nextNumber : (BitVec.ofNat 64 (position-1)).toNat=position-1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have nextRank : foldRank output.2=position-1 := by simp [foldRank,CounterFlow.counterWord,nextK,valueWord,nextNumber]
    exact ⟨⟨position-1,by omega,nextK,nextRoots,nextAcc,nextWorkspace⟩,by rw [nextRank,rankEq]; omega⟩
  have cost := ClockCost.ranked_loop_current source.code foldTest foldStep 53 (foldValid roots acc stp accel) foldRank priced progress source rfl ⟨k,inside,round,root,accumulator,workspace⟩
  have number : (BitVec.ofNat 64 k).toNat=k := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [fold_shape.1]
  simpa only [foldRank,CounterFlow.counterWord,round,Option.getD_some,valueWord,number] using cost

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.fold_arguments
#print axioms InitECandidate.Solver.Input.Progressive.fold_step_cost
#print axioms InitECandidate.Solver.Input.Progressive.fold_test_read
#print axioms InitECandidate.Solver.Input.Progressive.fold_loop_cost
