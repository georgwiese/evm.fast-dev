import InitECandidate.Solver.Input.RlpWrite.PutBeCall

namespace InitECandidate.Solver.Input.RlpWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def lengthTail (parameter : String) (tag : ExpHOL 64) : ProgHOL 64 :=
  .seq (.storeByte (localVar "dst") tag)
    (.seq (.call (some (none,none)) (ofString "rlp_put_be")
      [.op .add [localVar "dst",.const 1#64],localVar parameter,localVar "ll"])
      RlpLength.returnOnePlus)

/-- Shared literal long-form writer suffix, used by both scalar encoding and
RLP header writing. It includes the real tag store and put_be call. -/
theorem length_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst value tagValue : BitVec 64)
    (parameter : String) (count : Nat) (tag : ExpHOL 64) (small : count≤8)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (v : source.locals.lookup (ofString parameter)=some (.val (.word value)))
    (ll : source.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))))
    (tagRead : eval source tag=some (.val (.word tagValue)))
    (code : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : count+1≤source.clock) :
    ∃ target,evaluateHOLFiniteState source (lengthTail parameter tag)=
        (some (.returned (.val (.word (BitVec.ofNat 64 (count+1))))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-1-count} ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→target.memory query=source.memory query) := by
  classical
  have dstRead : eval source (localVar "dst")=some (.val (.word dst)) := by simp [eval,localVar,evalHOLExact,toExact,d]
  have mapZero : source.memaddrs (panByteAlignHOL (width:=64) dst) := by simpa using mapped 0 (by decide)
  have storeRun:=WitnessRadix.ByteStore.execute_word source (localVar "dst") tag dst tagValue dstRead tagRead mapZero
  let written:={source with memory:=WitnessRadix.ByteStore.put source.memory source.be dst (BitVec.ofNat 8 tagValue.toNat)}
  have dWritten : written.locals.lookup (ofString "dst")=some (.val (.word dst)):=d
  have vWritten : written.locals.lookup (ofString parameter)=some (.val (.word value)):=v
  have llWritten : written.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=ll
  have args : evalListHOLFinite written (h:=fun address=>Classical.propDecidable (written.memaddrs address))
      [.op .add [localVar "dst",.const 1#64],localVar parameter,localVar "ll"]=
      some [.val (.word (dst+1#64)),.val (.word value),.val (.word (BitVec.ofNat 64 count))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dWritten,vWritten,llWritten,valueIsWord,valueWord,wordOpHOL,wordOp]
  have shiftedAddress (index : Nat) : dst+1#64+BitVec.ofNat 64 index=dst+BitVec.ofNat 64 (index+1) := by
    rw [BitVec.ofNat_add]
    calc
      (dst+1#64)+BitVec.ofNat 64 index=dst+(1#64+BitVec.ofNat 64 index) := BitVec.add_assoc _ _ _
      _=dst+(BitVec.ofNat 64 index+1#64) := congrArg (fun word : BitVec 64=>dst+word) (BitVec.add_comm _ _)
  have putMapped : ∀ index<count,written.memaddrs (panByteAlignHOL (width:=64) (dst+1#64+BitVec.ofNat 64 index)) := by
    intro index inside
    rw [shiftedAddress]
    exact mapped (index+1) (by omega)
  obtain ⟨memory,putRun,putFrame⟩:=PutBe.call_execute written (dst+1#64) value count _ (by omega) args code putMapped enough
  let returned:={written with memory:=memory,clock:=written.clock-1-count}
  have llReturned : returned.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=ll
  have returnRun : evaluateHOLFiniteState returned RlpLength.returnOnePlus=
      (some (.returned (.val (.word (BitVec.ofNat 64 (count+1))))),emptyLocalsHOLFinite returned) := by
    simp [RlpLength.returnOnePlus,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,llReturned,valueIsWord,valueWord,
      wordOpHOL,wordOp,←BitVec.ofNat_add,Nat.add_comm,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  refine ⟨emptyLocalsHOLFinite returned,?_,rfl,?_⟩
  · rw [lengthTail,WitnessRadix.StateSteps.next_sequence source written _ _ storeRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence written returned _ _ putRun (by change source.clock-1-count≤source.clock; omega)]
    exact returnRun
  · intro query away
    have frame:=putFrame query (by intro index inside; rw [shiftedAddress]; exact away (index+1) (by omega))
    have outside : query≠panByteAlignHOL (width:=64) dst := by simpa using away 0 (by decide)
    exact frame.trans (WitnessRadix.ByteStore.away source.memory source.be dst query (BitVec.ofNat 8 tagValue.toNat) outside)

end InitECandidate.Solver.Input.RlpWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.length_tail_execute
