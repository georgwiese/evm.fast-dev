import InitECandidate.Solver.Mpt.ValueEncodedLenCost
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.TailCallNormal
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Mpt.ValueEncodedLen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.RlpLength

/-- A normal original value-size result is an actual nonwrapping size
between n and n+9, with all nonlocals preserved. Its positive-length
byte read and real tail callee are derived from the executed wrapper. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,length.toNat≤encoded ∧ encoded≤length.toNat+9 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ source.clock-target.clock≤11 ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have price:=body_cost source length fits installed nCell
  rw [normal] at price
  have shaped:=normal
  rw [body_shape] at shaped
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source target "fb" (.const 0#64) 0#64 afterFirst value rfl shaped
  let entered:=bind source "fb" 0#64
  obtain ⟨current,guardRun,tailRun⟩:=Input.sequence_returned entered inner guard tail value (fun returned=>(guard_safe.summary_full entered).2.1 returned) continued
  have len : entered.locals.lookup (ofString "n")=some (.val (.word length)):=
    (bind_lookup_other source "fb" "n" 0#64 (by decide)).trans nCell
  obtain ⟨first,fb,nextLen,frame⟩:=guard_normal entered current length len (bind_lookup_same _ _ _) guardRun
  have codes:=Input.LocalEffects.code_of_erase entered current frame
  have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [codes]; exact installed
  obtain ⟨callee,called,entryFb,entryLen⟩:=BytesSize.environment current.code.lookup first length (Input.OriginalRlp.rlp_bytes_encoded_len current.code currentInstalled)
  obtain ⟨_funded,built,run,_checked,tailEnd⟩:=Input.CallNormal.tail_callee_return current inner (ofString "rlp_bytes_encoded_len") arguments _ BytesSize.body callee .one
    (tail_arguments current first length fb nextLen) called value tailRun
  obtain ⟨encoded,lower,upper,number,answer,_calleePrice,kept⟩:=BytesSize.body_normal (callEntryStateHOLFinite current callee) built first length fits entryFb entryLen
    (Input.OriginalRlp.rlp_header_len current.code currentInstalled) (Input.OriginalRlp.rlp_be_len current.code currentInstalled) value run
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase built:=by rw [endpoint,tailEnd]; rfl
  exact ⟨encoded,lower,upper,number,answer,price,finalFrame.trans (kept.trans frame)⟩

/-- The real value-size wrapper agrees with the byte writer formula, using
only the source byte needed for the one-byte special case. -/
theorem body_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (first length : BitVec 64)
    (fits : length.toNat+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (firstRead : length=1#64→eval source (.loadByte (localVar "p"))=some (.val (.word first)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,encoded=BytesSize.encodedLength first length ∧ length.toNat≤encoded ∧ encoded≤length.toNat+9 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ source.clock-target.clock≤11 ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have price:=body_cost source length fits installed nCell
  rw [normal] at price
  have shaped:=normal
  rw [body_shape] at shaped
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source target "fb" (.const 0#64) 0#64 afterFirst value rfl shaped
  let entered:=bind source "fb" 0#64
  obtain ⟨current,guardRun,tailRun⟩:=Input.sequence_returned entered inner guard tail value (fun returned=>(guard_safe.summary_full entered).2.1 returned) continued
  have len : entered.locals.lookup (ofString "n")=some (.val (.word length)):=
    (bind_lookup_other source "fb" "n" 0#64 (by decide)).trans nCell
  obtain ⟨actualFirst,fb,nextLen,frame,byteRead⟩:=guard_normal_exact entered current length len (bind_lookup_same _ _ _) guardRun
  have sameRead : eval entered (.loadByte (localVar "p"))=eval source (.loadByte (localVar "p")):=by
    have pSame : entered.locals.lookup (ofString "p")=source.locals.lookup (ofString "p"):=bind_lookup_other source "fb" "p" 0#64 (by decide)
    simp only [eval,evalHOLExact,toExact,localVar,pSame]
    rfl
  have sameSize : BytesSize.encodedLength actualFirst length=BytesSize.encodedLength first length:=by
    by_cases one : length=1#64
    · have positive : 0<length.toNat:=by rw [one]; decide
      have equal : actualFirst=first:=by
        have values:=(byteRead positive).symm.trans (sameRead.trans (firstRead one))
        exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj values))
      rw [equal]
    · simp only [BytesSize.encodedLength,one,false_and,if_false]
  have codes:=Input.LocalEffects.code_of_erase entered current frame
  have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [codes]; exact installed
  obtain ⟨callee,called,entryFb,entryLen⟩:=BytesSize.environment current.code.lookup actualFirst length (Input.OriginalRlp.rlp_bytes_encoded_len current.code currentInstalled)
  obtain ⟨_funded,built,run,_checked,tailEnd⟩:=Input.CallNormal.tail_callee_return current inner (ofString "rlp_bytes_encoded_len") arguments _ BytesSize.body callee .one
    (tail_arguments current actualFirst length fb nextLen) called value tailRun
  obtain ⟨encoded,exactCount,lower,upper,number,answer,_calleePrice,kept⟩:=BytesSize.body_normal_exact (callEntryStateHOLFinite current callee) built actualFirst length fits entryFb entryLen
    (Input.OriginalRlp.rlp_header_len current.code currentInstalled) (Input.OriginalRlp.rlp_be_len current.code currentInstalled) value run
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase built:=by rw [endpoint,tailEnd]; rfl
  exact ⟨encoded,exactCount.trans sameSize,lower,upper,number,answer,price,finalFrame.trans (kept.trans frame)⟩

end InitECandidate.Solver.Mpt.ValueEncodedLen

#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.body_normal

#print axioms InitECandidate.Solver.Mpt.ValueEncodedLen.body_normal_exact
