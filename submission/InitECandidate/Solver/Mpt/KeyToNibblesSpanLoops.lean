import InitECandidate.Solver.Mpt.KeyToNibblesWriteFrame
import InitECandidate.Solver.Mpt.KeyToNibblesAnyLoops
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Carry the genuine byte-write footprint through a real loop, retaining
the actual output pointer and bounded counter for its next current state. -/
theorem loop_span_frame (test : ExpHOL 64) (loopBody : ProgHOL 64) (stride length : Nat)
    (positive : 0<stride) (small : length<2^64) (writes : Writes (2*stride) loopBody)
    (advance : Input.CounterFlow.Advances (ofString "i") stride loopBody)
    (summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,Input.LocalSummary (ofString "n") loopBody source)
    (reads : Input.CounterFlow.StrideReads test stride length)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (valid : Input.CounterFlow.StrideInvariant length source)
    (normal : evaluateHOLFiniteState source (.while test loopBody)=(none,target)) :
    SpanFrame source target out (2*length) ∧ target.locals.lookup (ofString "out")=some (.val (.word out)) ∧
      Input.CounterFlow.StrideInvariant length target := by
  let invariant:=fun current=>SpanFrame source current out (2*length) ∧ current.locals.lookup (ofString "out")=some (.val (.word out)) ∧
    Input.CounterFlow.StrideInvariant length current
  apply Input.loop_invariant_no_control source.code test loopBody (fun current=>(summary current).2.2) invariant _ source target rfl
    ⟨SpanFrame.refl source out (2*length),outCell,valid⟩ normal
  intro current codeEq currentValid observed actual nonzero funded post bodyRun
  obtain ⟨earlier,currentOut,currentCounter⟩:=currentValid
  have counter:=currentCounter
  obtain ⟨index,iCell,nCell,inside⟩:=counter
  have expected:=reads current index iCell nCell inside
  have active : index.toNat+stride≤length:=by
    by_cases active : index.toNat+stride≤length
    · exact active
    · exfalso
      rw [if_neg active] at expected
      have zero : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans expected
      exact nonzero zero
  obtain ⟨bodyFrame,nextOut⟩:=writes.normal (decClockHOLFinite current) post out index (2*length) (by omega) currentOut iCell bodyRun
  have kept : SpanFrame current post out (2*length):=⟨bodyFrame.fields,bodyFrame.memory⟩
  have transition:=(Input.CounterFlow.stride_transition test loopBody stride length positive small advance summary reads current currentCounter observed actual nonzero).2 funded
  rw [bodyRun] at transition
  exact ⟨earlier.trans source current post out (2*length) kept,nextOut,(transition (Or.inl rfl)).1⟩

/-- Both original normal loops protect the whole variable-length output
span; source byte contents and successful future writes are not premises. -/
theorem loops_span_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64) (length : Nat)
    (small : length+4<2^64) (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (valid : Input.CounterFlow.StrideInvariant length source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq blockLoop (.seq tailLoop afterTail))=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ SpanFrame source target out (2*length) := by
  have blockSummary:=Input.while_local_summary (ofString "n") blockCondition blockBody bodies_length_summary.1 source
  rw [←loop_shapes.1] at blockSummary
  obtain ⟨middle,blockRun,tailRun⟩:=Input.sequence_returned source target blockLoop (.seq tailLoop afterTail) value (fun returned=>blockSummary.2.1 returned) normal
  have realBlock:=blockRun
  rw [loop_shapes.1] at realBlock
  obtain ⟨blockFrame,nextOut,nextCounter⟩:=loop_span_frame blockCondition blockBody 4 length (by decide) (by omega) bodies_write_span.1 bodies_advance.1 bodies_length_summary.1 (block_reads length small) source middle out outCell valid realBlock
  have tailSummary:=Input.while_local_summary (ofString "n") tailCondition tailBody bodies_length_summary.2 middle
  rw [←loop_shapes.2] at tailSummary
  obtain ⟨last,tailLoopRun,returnRun⟩:=Input.sequence_returned middle target tailLoop afterTail value (fun returned=>tailSummary.2.1 returned) tailRun
  rw [loop_shapes.2] at tailLoopRun
  obtain ⟨tailFrame,lastOut,lastCounter⟩:=loop_span_frame tailCondition tailBody 1 length (by decide) (by omega) bodies_write_span.2 bodies_advance.2 bodies_length_summary.2 (tail_reads length (by omega)) middle last out nextOut nextCounter tailLoopRun
  rw [after_tail_shape] at returnRun
  obtain ⟨read,targetEq⟩:=Input.return_normal last target (.const 0#64) value returnRun
  have valueEq : value=.val (.word 0#64):=Option.some.inj read.symm
  have full:=blockFrame.trans source middle last out (2*length) tailFrame
  exact ⟨valueEq,⟨by rw [targetEq]; exact full.fields,by intro query outside; rw [targetEq]; exact full.memory query outside⟩⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.loop_span_frame
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.loops_span_frame
