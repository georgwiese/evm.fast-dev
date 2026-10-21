import InitECandidate.Solver.Input.PContainerBitMemory
import InitECandidate.Solver.Input.PContainerSuffixCost
import InitECandidate.Solver.Input.ShaPairMemory
import InitECandidate.Solver.Input.CopyZeroMemoryNormal
import InitECandidate.Solver.Input.HeapReleaseMemory

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original activity declaration/zeroing, bounded mask loop, final pair
and release preserve every word outside their actual temporary/output/SHA
buffers. All intermediate bindings come from the same normal execution. -/
theorem after_progressive_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (tmp out stp accel query : BitVec 64) (n : Nat) (short : n<32)
    (workspace : ShaPair.Workspace source stp accel)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (arena : AllocatedBytes.Arena tmp 64) (aligned : tmp.toNat%8=0)
    (tmpAway : CopyGeneral.Away tmp query 64) (stateAway : CopyGeneral.Away stp query 64)
    (accelAway : CopyGeneral.Away accel query 96) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterProgressive=(some (.returned value),post)) : post.memory query=source.memory query := by
  let act := tmp+32#64
  let entry := bind source "act" act
  have read : eval source (.op .add [localVar "tmp",.const 32#64])=some (.val (.word act)) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,temporary,valueIsWord,valueWord,wordOpHOL,wordOp,act]
  rw [body_shape.2.2.2.1] at run
  obtain ⟨actFinal,actRun,actEndpoint⟩ := declaration_return_word source post "act" _ act afterAct value read run
  have entryOther (name : String) (different : ofString "act"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other source "act" name act different
  have activity : entry.locals.lookup (ofString "act")=some (.val (.word act)) := bind_lookup_same _ _ _
  have actArena : AllocatedBytes.Arena act 32 := AllocatedBytes.Arena.subrange tmp 64 32 32 arena (by decide)
  have actNumber : act.toNat=tmp.toNat+32 := BitVec.toNat_add_of_lt (by change tmp.toNat+32<2^64; have h:=arena.upper; omega)
  have actAligned : act.toNat%8=0 := by rw [actNumber]; omega
  have actAway : CopyGeneral.Away act query 32 := CopyGeneral.Away.subrange tmp query 64 32 32 tmpAway (by decide)
  have zeroArgs : evalListHOLFinite entry (h:=fun address=>Classical.propDecidable (entry.memaddrs address)) zeroArguments=some (Zero.values act 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,localVar,activity,Zero.values]
  have zeroSafe : LocalPrefix (ofString "n") (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.2.2.1] at actRun
  obtain ⟨cleared,zeroRun,afterZeroRun⟩ := Input.sequence_returned entry actFinal _ afterZero value (zeroSafe.summary_full entry).2.1 actRun
  have zeroMemory := MemoryAt.zero_normal entry cleared zeroArguments act query 32 zeroArgs workspace.installed workspace.domain actArena actAligned (by decide) (fun offset inside=>(actAway offset inside).1) zeroRun
  have zeroGlobals (key : MlS) : GlobalEffects.Preserves key entry.code (.call (some (none,none)) (ofString "memzero") zeroArguments) :=
    GlobalEffects.call_body key entry.code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one (Zero.original_code entry.code workspace.installed) (Zero.globals key entry.code)
  have entryWorkspace := ShaPair.Workspace.of_fields source entry stp accel workspace rfl rfl rfl rfl
  have clearedWorkspace := ShaPair.Workspace.after entry cleared stp accel entryWorkspace _ none zeroRun (zeroGlobals (ofString "sha_st")) (zeroGlobals (ofString "sha_accel"))
  have clearedOther (name : String) : cleared.locals.lookup (ofString name)=entry.locals.lookup (ofString name) := CallNormal.ignored_lookup entry cleared (ofString name) (ofString "memzero") zeroArguments zeroRun
  rw [body_shape.2.2.2.2.2.1] at afterZeroRun
  obtain ⟨iFinal,iRun,iEndpoint⟩ := declaration_return_word cleared actFinal "i" (.const 0#64) 0#64 loopAndSuffix value rfl afterZeroRun
  let iEntry := bind cleared "i" 0#64
  have iOther (name : String) (different : ofString "i"≠ofString name) : iEntry.locals.lookup (ofString name)=cleared.locals.lookup (ofString name) := bind_lookup_other cleared "i" name 0#64 different
  have iActivity := ((iOther "act" (by decide)).trans (clearedOther "act")).trans activity
  have iCount := (((iOther "n" (by decide)).trans (clearedOther "n")).trans (entryOther "n" (by decide))).trans count
  rw [body_shape.2.2.2.2.2.2.1] at iRun
  have safe (name : String) (different : ofString name≠ofString "i") : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString name) bitLoop current := by
    rw [body_shape.2.2.2.2.2.2.2.1]
    exact while_local_summary (ofString name) test bitStep (bit_step_summary (ofString name) different)
  obtain ⟨folded,loopRun,pairSuffix⟩ := Input.sequence_returned iEntry iFinal bitLoop afterLoop value (safe "tmp" (by decide) iEntry).2.1 iRun
  have loopMemory := bit_loop_memory iEntry folded act query n 0 short (Nat.zero_le _) iActivity iCount (bind_lookup_same _ _ _) actAway loopRun
  have iWorkspace := ShaPair.Workspace.of_fields cleared iEntry stp accel clearedWorkspace rfl rfl rfl rfl
  have foldedWorkspace := ShaPair.Workspace.after iEntry folded stp accel iWorkspace bitLoop none loopRun (bit_loop_globals (ofString "sha_st") iEntry.code) (bit_loop_globals (ofString "sha_accel") iEntry.code)
  have foldedOther (name : String) (different : ofString name≠ofString "i") : folded.locals.lookup (ofString name)=iEntry.locals.lookup (ofString name) := by
    have summary := safe name different iEntry
    unfold LocalSummary at summary
    rw [loopRun] at summary
    exact summary.1 rfl
  have currentTmp := ((((foldedOther "tmp" (by decide)).trans (iOther "tmp" (by decide))).trans (clearedOther "tmp")).trans (entryOther "tmp" (by decide))).trans temporary
  have currentOut := ((((foldedOther "out" (by decide)).trans (iOther "out" (by decide))).trans (clearedOther "out")).trans (entryOther "out" (by decide))).trans output
  have currentAct := (foldedOther "act" (by decide)).trans iActivity
  have pairArgs : evalListHOLFinite folded (h:=fun address=>Classical.propDecidable (folded.memaddrs address)) shaArguments=some (ShaPair.values tmp act out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,shaArguments,localVar,currentTmp,currentOut,currentAct,ShaPair.values]
  rw [body_shape.2.2.2.2.2.2.2.2.2] at pairSuffix
  have pairSafe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "sha256_pair") shaArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨paired,pairRun,releaseRun⟩ := Input.sequence_returned folded iFinal _ afterSha value (pairSafe.summary_full folded).2.1 pairSuffix
  have pairMemory := ShaPair.call_memory folded paired tmp act out stp accel query foldedWorkspace (AllocatedBytes.Arena.weaken tmp 64 32 arena (by decide)) actArena stateAway accelAway outAway shaArguments pairArgs pairRun
  have fields := evaluation_fields folded paired _ none pairRun
  have tail := HeapScope.release_return_memory paired iFinal [localVar "mark"] query (fields.2.2.2.symm ▸ foldedWorkspace.installed) value releaseRun
  rw [actEndpoint,iEndpoint]
  exact tail.trans (pairMemory.trans (loopMemory.trans zeroMemory))

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.after_progressive_memory
