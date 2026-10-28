import InitECandidate.Solver.Input.CurrentHash.PContainerBitMemory
import InitECandidate.Solver.Input.CurrentHash.Sha256Memory
import InitECandidate.Solver.Input.CopyZeroMemoryNormal
import InitECandidate.Solver.Input.HeapReleaseMemory
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentHash.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterLoop=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape.2.2.2.2.2.2.2.2.2] at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "sha256_pair") shaArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (localVar "out")=some (.val (.word out)) := by
    simpa [evalHOLFinite,evalHOLExact,toExact,localVar] using output
  have pair := Sha256Memory.call_output_memory source middle (localVar "tmp") (localVar "act") (localVar "out") out query installed read
    (by intro offset inside; exact (outAway offset inside).2) normal
  have currentCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact installed
  exact (HeapScope.release_return_memory middle post [localVar "mark"] query currentCode value remaining).trans pair

theorem bit_loop_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (act out query : BitVec 64) (n index : Nat)
    (short : n≤256) (inside : index≤n) (installed : OriginalCode.Installed source.code)
    (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (actAway : CopyGeneral.Away act query 32) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source loopAndSuffix=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "out") bitLoop := by rw [body_shape.2.2.2.2.2.2.2.1]; exact .loop _ (bit_step_other _ (by decide))
  rw [body_shape.2.2.2.2.2.2.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have loopFrame := bit_loop_memory source middle act query n index short inside activity count position actAway normal
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  have currentCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact installed
  exact (after_loop_memory middle post out query currentCode ((summary.1 rfl).trans output) outAway value remaining).trans loopFrame

theorem after_zero_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (act out query : BitVec 64) (n : Nat)
    (short : n≤256) (installed : OriginalCode.Installed source.code)
    (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (actAway : CopyGeneral.Away act query 32) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterZero=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape.2.2.2.2.2.1] at actual
  apply MemoryAt.declaration_returned source post "i" (.const 0#64) 0#64 query loopAndSuffix value rfl _ actual
  intro inner remaining
  let entry := bind source "i" 0#64
  have kept (name : String) (different : ofString "i"≠ofString name) := bind_lookup_other source "i" name 0#64 different
  exact bit_loop_suffix_memory entry inner act out query n 0 short (Nat.zero_le _) installed ((kept "act" (by decide)).trans activity)
    ((kept "n" (by decide)).trans count) (bind_lookup_same _ _ _) ((kept "out" (by decide)).trans output) actAway outAway value remaining

/-- Actual activity declaration/clear/loop, final software pair and release.
The same caller's fixed field count must fit the32-byte activity mask. -/
theorem after_progressive_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (tmp out query : BitVec 64) (n : Nat)
    (short : n≤256) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (arena : AllocatedBytes.Arena tmp 64) (aligned : tmp.toNat%8=0)
    (tmpAway : CopyGeneral.Away tmp query 64) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterProgressive=(some (.returned value),post)) : post.memory query=source.memory query := by
  let act := tmp+32#64
  have read : eval source (.op .add [localVar "tmp",.const 32#64])=some (.val (.word act)) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,temporary,valueIsWord,valueWord,wordOpHOL,wordOp,act]
  have actArena : AllocatedBytes.Arena act 32 := AllocatedBytes.Arena.subrange tmp 64 32 32 arena (by decide)
  have actAligned : act.toNat%8=0 := byteAddress_aligned tmp 32 aligned (by decide) (by have h:=arena.upper; omega)
  have actAway := CopyGeneral.Away.subrange tmp query 64 32 32 tmpAway (by decide)
  rw [body_shape.2.2.2.1] at actual
  apply MemoryAt.declaration_returned source post "act" _ act query afterAct value read _ actual
  intro inner remaining
  let entry := bind source "act" act
  have activity : entry.locals.lookup (ofString "act")=some (.val (.word act)) := bind_lookup_same _ _ _
  have kept (name : String) (different : ofString "act"≠ofString name) := bind_lookup_other source "act" name act different
  have args : evalListHOLFinite entry (h:=fun address=>Classical.propDecidable (entry.memaddrs address)) zeroArguments=some (Zero.values act 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,zeroArguments,localVar,activity,Zero.values]
  have safe : LocalPrefix (ofString "act") (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.2.2.1] at remaining
  obtain ⟨middle,normal,returned⟩ := Input.sequence_returned entry inner _ _ value (safe.summary_full entry).2.1 remaining
  have front := MemoryAt.zero_normal entry middle zeroArguments act query 32 args installed domain actArena actAligned (by decide)
    (by intro offset inside; exact (actAway offset inside).1) normal
  have after (name : String) := CallNormal.ignored_lookup entry middle (ofString name) (ofString "memzero") zeroArguments normal
  have currentCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields entry middle _ none normal).2.2.2]; exact installed
  exact (after_zero_memory middle inner act out query n short currentCode ((after "act").trans activity)
    (((after "n").trans (kept "n" (by decide))).trans count) (((after "out").trans (kept "out" (by decide))).trans output)
    actAway outAway value returned).trans front

end InitECandidate.Solver.Input.CurrentHash.PContainer

#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_loop_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.bit_loop_suffix_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_zero_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_progressive_memory
