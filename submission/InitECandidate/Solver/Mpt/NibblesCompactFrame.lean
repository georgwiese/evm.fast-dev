import InitECandidate.Solver.Mpt.NibblesCompactLoopNormal
import InitECandidate.Solver.Mpt.KeyToNibblesWriteFrame
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.NibblesCompact
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open KeyToNibbles (SpanFrame writeMetadata)

theorem span_of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : BitVec 64) (size : Nat)
    (same : Input.LocalEffects.erase target=Input.LocalEffects.erase source) : SpanFrame source target destination size := by
  refine ⟨?_,?_⟩
  · exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with memory:=fun _=>.word 0#64}) same
  · intro query away
    exact congrFun (Input.LocalEffects.memory_of_erase source target same) query

theorem byte_store_span (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : BitVec 64) (size offset : Nat)
    (address value : ExpHOL 64) (inside : offset<size)
    (read : eval source address=some (.val (.word (byteAddress destination offset))))
    (normal : evaluateHOLFiniteState source (.storeByte address value)=(none,target)) : SpanFrame source target destination size := by
  have frame:=Input.byte_store_normal_frame source target address value (byteAddress destination offset) read normal
  refine ⟨?_,fun query away=>frame.2 query (away offset inside)⟩
  rw [frame.1]
  rfl

theorem step_span (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : BitVec 64) (length : Nat)
    (valid : OutputValid length source) (active : (Input.CounterFlow.counterWord source (ofString "i")).toNat<length)
    (destinationCell : source.locals.lookup (ofString "dst")=some (.val (.word destination)))
    (normal : evaluateHOLFiniteState source step=(none,target)) : SpanFrame source target destination (length/2+1) := by
  obtain ⟨index,indexCell,lengthCell,inside,parity⟩:=valid.1
  obtain ⟨output,outputCell,relation⟩:=valid.2
  have currentNumber : (Input.CounterFlow.counterWord source (ofString "i")).toNat=index.toNat:=by
    simp [Input.CounterFlow.counterWord,indexCell,valueWord]
  rw [currentNumber] at active relation
  have outputInside : output.toNat<length/2+1:=by omega
  rw [body_shapes.2.2.2.2.2.2.1,store_pair_shape] at normal
  obtain ⟨stored,storeRun,tailRun⟩:=Input.sequence_none source target (.storeByte pairAddress pairValue) (.seq advance advanceOutput) normal
  have read : eval source pairAddress=some (.val (.word (byteAddress destination output.toNat))):=by
    simp [eval,pairAddress,evalHOLExact,evalListHOLExact,toExact,localVar,destinationCell,outputCell,valueIsWord,valueWord,wordOpHOL,wordOp,byteAddress]
  have first:=byte_store_span source stored destination (length/2+1) output.toNat pairAddress pairValue outputInside read storeRun
  have pure:=Input.LocalEffects.sequence stored.code advance advanceOutput (Input.LocalEffects.assign stored.code _ _) (Input.LocalEffects.assign stored.code _ _) stored rfl
  rw [tailRun] at pure
  exact first.trans source stored target destination (length/2+1) (span_of_erase stored target destination _ pure)

theorem loop_span (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : BitVec 64) (length : Nat)
    (small : length<2^64) (valid : OutputValid length source)
    (destinationCell : source.locals.lookup (ofString "dst")=some (.val (.word destination)))
    (normal : evaluateHOLFiniteState source loop=(none,target)) : SpanFrame source target destination (length/2+1) := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>OutputValid length current ∧
    current.locals.lookup (ofString "dst")=some (.val (.word destination)) ∧ SpanFrame source current destination (length/2+1)
  have reached:=Input.loop_invariant_summary source.code (ofString "n") test step
    (step_summary (ofString "n") (by decide) (by decide)) invariant (by
      intro current codeEq ready word read nonzero funded post bodyRun
      have output:=output_transition length small current post ready.1 word read nonzero funded bodyRun
      obtain ⟨index,indexCell,lengthCell,inside,parity⟩:=ready.1.1
      have expected:=test_read current length index small indexCell lengthCell
      have active : (Input.CounterFlow.counterWord current (ofString "i")).toNat<length:=by
        have less : index.toNat<length:=by
          by_contra inactive
          rw [if_neg inactive] at expected
          have zero : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
          exact nonzero zero
        simpa only [Input.CounterFlow.counterWord,indexCell,Option.getD_some,valueWord] using less
      have frame:=step_span (decClockHOLFinite current) post destination length ready.1 active ready.2.1 bodyRun
      have safe:=step_summary (ofString "dst") (by decide) (by decide) (decClockHOLFinite current)
      unfold Input.LocalSummary at safe
      rw [bodyRun] at safe
      have currentFrame : SpanFrame current post destination (length/2+1):=
        ⟨by simpa only [writeMetadata,Input.MemoryMetadata.erase,decClockHOLFinite] using frame.fields,frame.memory⟩
      exact ⟨output,(safe.1 rfl).trans ready.2.1,ready.2.2.trans source current post destination _ currentFrame⟩)
    source target rfl ⟨valid,destinationCell,KeyToNibbles.SpanFrame.refl source destination _⟩ (by rw [←body_shapes.2.2.2.2.2.1]; exact normal)
  exact reached.2.2

end InitECandidate.Solver.Mpt.NibblesCompact

#print axioms InitECandidate.Solver.Mpt.NibblesCompact.span_of_erase
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.byte_store_span
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.step_span
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.loop_span
