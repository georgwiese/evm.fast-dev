import InitECandidate.Solver.Mpt.NibblesCompactFrame
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Mpt.NibblesCompact
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open KeyToNibbles (SpanFrame writeMetadata)

theorem header_span (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : BitVec 64) (length : Nat)
    (destinationCell : source.locals.lookup (ofString "dst")=some (.val (.word destination)))
    (normal : evaluateHOLFiniteState source header=(none,target)) : SpanFrame source target destination (length/2+1) := by
  have read : eval source (localVar "dst")=some (.val (.word (byteAddress destination 0))):=by
    simpa [eval,evalHOLExact,toExact,localVar,byteAddress] using destinationCell
  rw [body_shapes.2.2.2.2.2.2.2,evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address)) evenTest=value at normal
  cases value with
  | none=>cases normal
  | some value=>
    cases value with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word word=>
        simp only at normal
        split at normal
        · obtain ⟨stored,storeRun,assignRun⟩:=Input.sequence_none source target oddStore _ normal
          have first:=byte_store_span source stored destination (length/2+1) 0 _ _ (by omega) read storeRun
          have frame:=Input.LocalEffects.assign stored.code (ofString "i") (.const 1#64) stored rfl
          rw [assignRun] at frame
          exact first.trans source stored target destination _ (span_of_erase stored target destination _ frame)
        · exact byte_store_span source target destination (length/2+1) 0 _ _ (by omega) read normal

/-- The actual unchanged writer returns exactly floor(n/2)+1 and changes
only the backing words of that many bytes at its real destination. Source
bytes need not be postulated readable: failures cannot produce this return. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length leaf destination : BitVec 64)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (leafCell : source.locals.lookup (ofString "is_leaf")=some (.val (.word leaf)))
    (destinationCell : source.locals.lookup (ofString "dst")=some (.val (.word destination)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ output : BitVec 64,value=.val (.word output) ∧ output.toNat=length.toNat/2+1 ∧
      source.clock-target.clock≤length.toNat/2 ∧ SpanFrame source target destination (length.toNat/2+1) := by
  have price:=body_cost source length leaf lengthCell leafCell
  rw [normal] at price
  have flagRead : eval source flagExpression=some (.val (.word (leaf*2#64))):=by
    simp [eval,flagExpression,evalHOLExact,evalListHOLExact,toExact,localVar,leafCell,valueIsWord,valueWord,panOpHOL]
  have shaped:=normal
  rw [body_shapes.1] at shaped
  obtain ⟨flagInner,flagRun,flagEnd⟩:=Input.declaration_return_word source target "flag" flagExpression (leaf*2#64) afterFlag value flagRead shaped
  let flagged:=bind source "flag" (leaf*2#64)
  rw [body_shapes.2.1] at flagRun
  obtain ⟨indexInner,indexRun,indexEnd⟩:=Input.declaration_return_word flagged flagInner "i" (.const 0#64) 0#64 afterCounter value rfl flagRun
  let entered:=bind flagged "i" 0#64
  rw [body_shapes.2.2.1] at indexRun
  obtain ⟨current,headerRun,outputRun⟩:=Input.sequence_returned entered indexInner header outputScope value
    (header_summary (ofString "n") (by decide) entered).2.1 indexRun
  have currentLength : entered.locals.lookup (ofString "n")=some (.val (.word length)):=
    (bind_lookup_other flagged "i" "n" 0#64 (by decide)).trans
      ((bind_lookup_other source "flag" "n" (leaf*2#64) (by decide)).trans lengthCell)
  have enteredDestination : entered.locals.lookup (ofString "dst")=some (.val (.word destination)):=
    (bind_lookup_other flagged "i" "dst" 0#64 (by decide)).trans
      ((bind_lookup_other source "flag" "dst" (leaf*2#64) (by decide)).trans destinationCell)
  obtain ⟨index,nextLength⟩:=header_normal entered current length currentLength (bind_lookup_same _ _ _) headerRun
  have headerFrame:=header_span entered current destination length.toNat enteredDestination headerRun
  have destinationSaved:=header_summary (ofString "dst") (by decide) entered
  unfold Input.LocalSummary at destinationSaved
  rw [headerRun] at destinationSaved
  have currentDestination:=(destinationSaved.1 rfl).trans enteredDestination
  rw [body_shapes.2.2.2.1] at outputRun
  obtain ⟨outputInner,continued,outputEnd⟩:=Input.declaration_return_word current indexInner "o" (.const 1#64) 1#64 afterOutput value rfl outputRun
  let outputReady:=bind current "o" 1#64
  have actualIndex : outputReady.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (length.toNat%2)))):=
    (bind_lookup_other current "o" "i" 1#64 (by decide)).trans index
  have actualLength : outputReady.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length.toNat))):=by
    simpa using (bind_lookup_other current "o" "n" 1#64 (by decide)).trans nextLength
  have parityNumber : (BitVec.ofNat 64 (length.toNat%2)).toNat=length.toNat%2:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show length.toNat%2<2^64 by omega)]
  have valid : OutputValid length.toNat outputReady:=by
    refine ⟨⟨BitVec.ofNat 64 (length.toNat%2),actualIndex,actualLength,?_,?_⟩,1#64,bind_lookup_same _ _ _,?_⟩
    · rw [parityNumber]; omega
    · rw [parityNumber]; omega
    · simp only [Input.CounterFlow.counterWord,actualIndex,Option.getD_some,valueWord,parityNumber]
      change 1=length.toNat%2/2+1
      omega
  rw [body_shapes.2.2.2.2.1] at continued
  have never:=(Input.while_local_summary (ofString "n") test step (step_summary (ofString "n") (by decide) (by decide)) outputReady).2.1
  rw [←body_shapes.2.2.2.2.2.1] at never
  obtain ⟨last,loopRun,returnRun⟩:=Input.sequence_returned outputReady outputInner loop (.return (localVar "o")) value never continued
  obtain ⟨_index,out,outCell,size⟩:=loop_normal outputReady last length.toNat length.isLt valid loopRun
  have loopFrame:=loop_span outputReady last destination length.toNat length.isLt valid
    ((bind_lookup_other current "o" "dst" 1#64 (by decide)).trans currentDestination) loopRun
  obtain ⟨returned,returnEnd⟩:=Input.return_normal last outputInner (localVar "o") value returnRun
  have answer : value=.val (.word out):=by
    have read : eval last (localVar "o")=some (.val (.word out)):=by simpa only [eval,evalHOLExact,toExact,localVar] using outCell
    exact Option.some.inj (returned.symm.trans read)
  have finalFrame : SpanFrame last target destination (length.toNat/2+1):=by
    rw [flagEnd,indexEnd,outputEnd,returnEnd]
    exact ⟨rfl,by intro query away; rfl⟩
  have throughLoop : SpanFrame current last destination (length.toNat/2+1):=⟨loopFrame.fields,loopFrame.memory⟩
  have throughHeader:=headerFrame.trans entered current last destination _ throughLoop
  have fromSource : SpanFrame source last destination (length.toNat/2+1):=⟨throughHeader.fields,throughHeader.memory⟩
  exact ⟨out,answer,size,price,fromSource.trans source last target destination _ finalFrame⟩

end InitECandidate.Solver.Mpt.NibblesCompact

#print axioms InitECandidate.Solver.Mpt.NibblesCompact.header_span
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.body_normal
