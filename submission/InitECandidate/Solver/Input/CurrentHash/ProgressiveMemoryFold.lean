import InitECandidate.Solver.Input.ProgressiveFoldProgram
import InitECandidate.Solver.Input.CurrentHash.Sha256Memory
import InitECandidate.Solver.Input.CopyReturnMemory
import InitECandidate.Solver.Input.MemoryNormal

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryFold
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Progressive

theorem step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (acc query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (accLocal : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (away : CopyGeneral.Away acc query 32) (actual : evaluateHOLFiniteState source foldStep=(none,post)) : post.memory query=source.memory query := by
  rw [fold_shape.2.1] at actual
  obtain ⟨middle,normal,called⟩ := Input.sequence_none source post decrement _ actual
  have safe : LocalPrefix (ofString "acc") decrement := .assign _ _ (by decide)
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  have accMiddle := (summary.1 rfl).trans accLocal
  have read : evalHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) (localVar "acc")=some (.val (.word acc)) := by
    simpa [evalHOLFinite,evalHOLExact,toExact,localVar] using accMiddle
  have currentCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact installed
  have hashed := Sha256Memory.call_output_memory middle post
    (.op .add [localVar "roots",.panop .mul [localVar "k",.const 32#64]]) (localVar "acc") (localVar "acc") acc query currentCode read
    (by intro offset inside; exact (away offset inside).2) called
  have assigned := MemoryAt.assign_current source .local (ofString "k") decrementExpression query
  change (evaluateHOLFiniteState source decrement).2.memory query=source.memory query at assigned
  rw [normal] at assigned
  exact hashed.trans assigned

/-- The current fold only writes its actual accumulator. Its memory frame
needs no root-input mapping, digest values or assumed final fold count. -/
theorem loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (acc query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (accLocal : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (away : CopyGeneral.Away acc query 32) (actual : evaluateHOLFiniteState source foldLoop=(none,post)) : post.memory query=source.memory query := by
  rw [fold_shape.1] at actual
  apply MemoryAt.loop_normal source.code (ofString "acc") foldTest foldStep query
    (fun current=>(fold_other (ofString "acc") (by decide)).summary_full current)
    (fun current=>current.locals.lookup (ofString "acc")=some (.val (.word acc))) _ source post rfl accLocal actual
  intro current codeEq ready word read nonzero funded target continued
  have currentCode : OriginalCode.Installed current.code := by rw [codeEq]; exact installed
  have memory := step_memory (decClockHOLFinite current) target acc query currentCode ready away continued
  have summary := (fold_other (ofString "acc") (by decide)).summary_full (decClockHOLFinite current)
  unfold LocalSummary at summary
  rw [continued] at summary
  exact ⟨(summary.1 rfl).trans ready,memory⟩

structure Params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (acc out : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))

theorem Params.after_prefix {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {acc out : BitVec 64}
    (data : Params source acc out) (program : ProgHOL 64) (accSafe : LocalPrefix (ofString "acc") program)
    (outSafe : LocalPrefix (ofString "out") program) (actual : evaluateHOLFiniteState source program=(none,post)) : Params post acc out := by
  have fields := evaluation_fields source post _ none actual
  have installed : OriginalCode.Installed post.code := by rw [fields.2.2.2]; exact data.installed
  have accSummary := accSafe.summary_full source
  have outSummary := outSafe.summary_full source
  unfold LocalSummary at accSummary outSummary
  rw [actual] at accSummary outSummary
  exact ⟨installed,fields.1.trans data.domain,(accSummary.1 rfl).trans data.accumulator,(outSummary.1 rfl).trans data.output⟩

theorem output_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (acc out query : BitVec 64)
    (data : Params source acc out) (accArena : AllocatedBytes.Arena acc 32) (outArena : AllocatedBytes.Arena out 32)
    (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterFold=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) outputArguments=some (CopyGeneral.values out acc 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,outputArguments,localVar,data.accumulator,data.output,CopyGeneral.values]
  rw [fold_shape.2.2.2.2.2] at actual
  exact MemoryAt.copy_release_returned source post outputArguments [localVar "mark"] acc out query 32 data.installed data.domain args accArena outArena outAway value actual

theorem after_zero_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (acc out query : BitVec 64)
    (data : Params source acc out) (accArena : AllocatedBytes.Arena acc 32) (outArena : AllocatedBytes.Arena out 32)
    (accAway : CopyGeneral.Away acc query 32) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterZeroAcc=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe (name : String) (different : ofString name≠ofString "k") : LocalPrefix (ofString name) foldLoop := by
    rw [fold_shape.1]
    exact .loop _ (fold_other (ofString name) different)
  rw [fold_shape.2.2.2.2.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value ((safe "acc" (by decide)).summary_full source).2.1 actual
  have front := loop_memory source middle acc query data.installed data.accumulator accAway normal
  have next := data.after_prefix _ (safe "acc" (by decide)) (safe "out" (by decide)) normal
  exact (output_memory middle post acc out query next accArena outArena outAway value remaining).trans front

/-- Complete actual clear/fold/output/release suffix. -/
theorem suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (acc out query : BitVec 64)
    (data : Params source acc out) (accArena : AllocatedBytes.Arena acc 32) (outArena : AllocatedBytes.Arena out 32) (aligned : acc.toNat%8=0)
    (accAway : CopyGeneral.Away acc query 32) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterLoop=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values acc 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,zeroArguments,localVar,data.accumulator,Zero.values]
  have safe (name : String) : LocalPrefix (ofString name) (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [fold_shape.2.2.2.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value ((safe "acc").summary_full source).2.1 actual
  have front := MemoryAt.zero_normal source middle zeroArguments acc query 32 args data.installed data.domain accArena aligned (by decide)
    (by intro offset inside; exact (accAway offset inside).1) normal
  have next := data.after_prefix _ (safe "acc") (safe "out") normal
  exact (after_zero_memory middle post acc out query next accArena outArena accAway outAway value remaining).trans front

end InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryFold

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryFold.step_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryFold.loop_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryFold.Params.after_prefix
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryFold.output_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryFold.after_zero_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryFold.suffix_memory
