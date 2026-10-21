import InitECandidate.Solver.Mpt.CompactToNibblesOdd
import InitECandidate.Solver.Mpt.KeyToNibblesWriteFrame
import InitECandidate.Solver.Input.LocalSummaryConditional

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem odd_local_summary {F : Type} (key : MlS) (other : key≠ofString "k")
    (source : PanSemStateFiniteExact 64 F) : Input.LocalSummary key oddGuard source :=
  Input.local_summary_conditional key oddTest oddWrite .skip
    (Input.local_summary_sequence key _ _ (Input.byte_store_local key _ _) (Input.LocalPrefix.assign _ _ other).summary_full)
    Input.LocalPrefix.skip.summary_full source

theorem odd_no_return {F : Type} (source : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState source oddGuard).1≠some (.returned value):=
  (odd_local_summary (ofString "n") (by decide) source).2.1 value

/-- The actual optional nibble writes only the output's first backing word
and retains every nonmemory field apart from its local k assignment. -/
theorem odd_span_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (out odd : BitVec 64)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (oddCell : source.locals.lookup (ofString "odd")=some (.val (.word odd)))
    (normal : evaluateHOLFiniteState source oddGuard=(none,target)) : KeyToNibbles.SpanFrame source target out 1 := by
  by_cases zero : odd=0#64
  · have skipped : evaluateHOLFiniteState source oddGuard=(none,source):=by
      simp [oddGuard,oddTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,oddCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    have same : target=source:=congrArg Prod.snd (normal.symm.trans skipped)
    rw [same]
    exact KeyToNibbles.SpanFrame.refl source out 1
  · have taken : evaluateHOLFiniteState source oddGuard=evaluateHOLFiniteState source oddWrite:=by
      simp [oddGuard,oddTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,oddCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [taken] at normal
    obtain ⟨middle,storeRun,assignRun⟩:=Input.sequence_none source target _ _ normal
    have read : eval source (localVar "out")=some (.val (.word out)):=by simp [eval,evalHOLExact,localVar,toExact,outCell]
    obtain ⟨middleEq,memory⟩:=Input.byte_store_normal_frame source middle (localVar "out") (.op .and [localVar "c0",.const 15#64]) out read storeRun
    have targetEq:=Input.assign_none middle target "k" (.const 1#64) 1#64 rfl assignRun
    refine ⟨?_,?_⟩
    · rw [targetEq]
      have fields:=congrArg KeyToNibbles.writeMetadata middleEq
      exact fields
    · intro query outside
      rw [targetEq]
      apply memory query
      simpa only [byteAddress,BitVec.add_zero] using outside 0 (by decide)

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.odd_local_summary
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.odd_no_return
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.odd_span_frame
