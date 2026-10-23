import InitECandidate.Solver.Mpt.NodeRlpBeginProgram

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def storedMemory (memory : BitVec 64→HolWordLab 64) (frame buffer length payload : BitVec 64) : BitVec 64→HolWordLab 64:=
  StoreWord.put (StoreWord.put (StoreWord.put memory (frame+24#64) buffer) (frame+32#64) length) (frame+40#64) payload

theorem stored_fields (memory : BitVec 64→HolWordLab 64) (frame buffer length payload : BitVec 64) :
    storedMemory memory frame buffer length payload (frame+24#64)=.word buffer ∧
      storedMemory memory frame buffer length payload (frame+32#64)=.word length ∧
      storedMemory memory frame buffer length payload (frame+40#64)=.word payload := by
  simp [storedMemory,StoreWord.put,BitVec.add_right_inj]

theorem stored_away (memory : BitVec 64→HolWordLab 64) (frame buffer length payload query : BitVec 64)
    (first : query≠frame+24#64) (second : query≠frame+32#64) (third : query≠frame+40#64) :
    storedMemory memory frame buffer length payload query=memory query := by
  simp only [storedMemory,StoreWord.put,if_neg first,if_neg second,if_neg third]

theorem frame_address (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (offset : Nat)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame))) :
    eval source (frameAddress offset)=some (.val (.word (frame+BitVec.ofNat 64 offset))) := by
  simp [eval,frameAddress,evalHOLExact,evalListHOLExact,toExact,localVar,frameCell,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- The real footer derives all three mapped frame words and its exact
stores from observed normal execution; no successful future store is supplied. -/
theorem footer_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame buffer length payload : BitVec 64)
    (frameCell : source.locals.lookup (ofString "fr")=some (.val (.word frame)))
    (bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word buffer)))
    (lengthCell : source.locals.lookup (ofString "clen")=some (.val (.word length)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source footer=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧
      target=emptyLocalsHOLFinite {source with memory:=storedMemory source.memory frame buffer length payload} ∧
      source.memaddrs (frame+24#64) ∧ source.memaddrs (frame+32#64) ∧ source.memaddrs (frame+40#64) := by
  rw [footer_shape] at normal
  obtain ⟨first,firstRun,firstTail⟩:=Input.sequence_returned source target _ _ value ((Input.LocalPrefix.store (key:=ofString "fr") _ _).summary_full source).2.1 normal
  have bufferRead : eval source (localVar "cbuf")=some (.val (.word buffer)):=by simpa only [eval,evalHOLExact,toExact,localVar] using bufferCell
  obtain ⟨firstMapped,firstEq⟩:=Input.word_store_normal source first _ _ (frame+24#64) buffer (frame_address source frame 24 frameCell) bufferRead firstRun
  subst first
  let firstState:={source with memory:=StoreWord.put source.memory (frame+24#64) buffer}
  obtain ⟨second,secondRun,secondTail⟩:=Input.sequence_returned firstState target _ _ value ((Input.LocalPrefix.store (key:=ofString "fr") _ _).summary_full firstState).2.1 firstTail
  have lengthRead : eval firstState (localVar "clen")=some (.val (.word length)):=by simpa only [eval,evalHOLExact,toExact,localVar] using lengthCell
  obtain ⟨secondMapped,secondEq⟩:=Input.word_store_normal firstState second _ _ (frame+32#64) length (frame_address firstState frame 32 frameCell) lengthRead secondRun
  subst second
  let secondState:={firstState with memory:=StoreWord.put firstState.memory (frame+32#64) length}
  obtain ⟨third,thirdRun,returnRun⟩:=Input.sequence_returned secondState target _ _ value ((Input.LocalPrefix.store (key:=ofString "fr") _ _).summary_full secondState).2.1 secondTail
  have payloadRead : eval secondState (localVar "payload")=some (.val (.word payload)):=by simpa only [eval,evalHOLExact,toExact,localVar] using payloadCell
  obtain ⟨thirdMapped,thirdEq⟩:=Input.word_store_normal secondState third _ _ (frame+40#64) payload (frame_address secondState frame 40 frameCell) payloadRead thirdRun
  obtain ⟨returned,endpoint⟩:=Input.return_normal third target (.const 0#64) value returnRun
  have answer : value=.val (.word 0#64):=Option.some.inj returned.symm
  exact ⟨answer,by rw [endpoint,thirdEq]; rfl,firstMapped,secondMapped,thirdMapped⟩

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.stored_fields
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.stored_away
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.frame_address
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.footer_normal
