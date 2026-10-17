import InitECandidate.Solver.Input.RlpWrite.LengthTail

namespace InitECandidate.Solver.Input.RlpWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def shortForm (tag : ExpHOL 64) : ProgHOL 64 := .seq (.storeByte (localVar "dst") tag) (.return (.const 1#64))
def longForm (parameter : String) (tag : ExpHOL 64) : ProgHOL 64 :=
  .decCall (ofString "ll") .one (ofString "rlp_be_len") [localVar parameter] (lengthTail parameter tag)

theorem short_form_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst tagValue : BitVec 64) (tag : ExpHOL 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst))) (read : eval source tag=some (.val (.word tagValue)))
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) dst)) :
    ∃ target,evaluateHOLFiniteState source (shortForm tag)=(some (.returned (.val (.word 1#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory} ∧
      (∀ query,query≠panByteAlignHOL (width:=64) dst→target.memory query=source.memory query) := by
  classical
  have dstRead : eval source (localVar "dst")=some (.val (.word dst)) := by simp [eval,localVar,evalHOLExact,toExact,d]
  have stored:=WitnessRadix.ByteStore.execute_word source (localVar "dst") tag dst tagValue dstRead read mapped
  let written:={source with memory:=WitnessRadix.ByteStore.put source.memory source.be dst (BitVec.ofNat 8 tagValue.toNat)}
  refine ⟨emptyLocalsHOLFinite written,?_,rfl,?_⟩
  · rw [shortForm,WitnessRadix.StateSteps.next_sequence source written _ _ stored (Nat.le_refl _)]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  · intro query away
    exact WitnessRadix.ByteStore.away source.memory source.be dst query (BitVec.ofNat 8 tagValue.toNat) away

/-- Real be_len call and the complete writer suffix, including restored ll.
All actual stores stay within nine bytes and at most18 source clocks are paid. -/
theorem long_form_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst value : BitVec 64)
    (parameter : String) (tag : ExpHOL 64) (tagValue : Nat→BitVec 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word value)))
    (tagRead : ∀ count≤8,eval (bind {source with clock:=source.clock-1-count} "ll" (BitVec.ofNat 64 count)) tag=some (.val (.word (tagValue count))))
    (dstNe : ofString "ll"≠ofString "dst") (parameterNe : ofString "ll"≠ofString parameter)
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 18≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤18 ∧
      evaluateHOLFiniteState source (longForm parameter tag)=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→target.memory query=source.memory query) := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar parameter]=some (RlpLength.Be.values value) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,v,RlpLength.Be.values]
  obtain ⟨count,bound,called⟩:=RlpLength.Be.call_execute source value "ll" [localVar parameter] (lengthTail parameter tag) args beCode (by omega)
  let entry:=bind {source with clock:=source.clock-1-count} "ll" (BitVec.ofNat 64 count)
  have dEntry : entry.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (bind_lookup_other _ "ll" "dst" _ dstNe).trans d
  have vEntry : entry.locals.lookup (ofString parameter)=some (.val (.word value)):=
    (bind_lookup_other _ "ll" parameter _ parameterNe).trans v
  have llEntry : entry.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=bind_lookup_same _ _ _
  obtain ⟨target,tailRun,frame,memory⟩:=length_tail_execute entry dst value (tagValue count) parameter count tag bound dEntry vEntry llEntry (tagRead count bound) putCode mapped
    (by change count+1≤source.clock-1-count; omega)
  let final:=restore source "ll" target
  let paid:=2*count+2
  refine ⟨final,count+1,paid,by omega,by omega,by dsimp [paid]; omega,?_,?_,memory⟩
  · rw [longForm,called,tailRun]
  · change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid}
    rw [frame]
    have subtract : source.clock-1-count-1-count=source.clock-paid := by dsimp [paid]; omega
    change emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-1-count-1-count}=
      emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid}
    rw [subtract]

end InitECandidate.Solver.Input.RlpWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.short_form_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.long_form_execute
