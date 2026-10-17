import InitECandidate.Solver.Input.RlpWrite.Forms

namespace InitECandidate.Solver.Input.RlpWrite.WordWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_encode_word with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "dst",.one),(ofString "w",.one)]
def zeroTest : ExpHOL 64 := .cmp .equal (localVar "w") (.const 0#64)
def shortTest : ExpHOL 64 := .cmp .lower (localVar "w") (.const 128#64)
def longTag : ExpHOL 64 := .op .add [.const 128#64,localVar "ll"]
def zeroGuard : ProgHOL 64 := .ite zeroTest (shortForm (.const 128#64)) .skip
def shortGuard : ProgHOL 64 := .ite shortTest (shortForm (localVar "w")) .skip

theorem body_shape : body=.seq zeroGuard (.seq shortGuard (longForm "w" longTag)) := by
  simp only [body,Guest.guestFn_rlp_encode_word,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    zeroGuard,zeroTest,shortGuard,shortTest,shortForm,longForm,longTag,lengthTail,RlpLength.returnOnePlus,localVar]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst w : BitVec 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (value : source.locals.lookup (ofString "w")=some (.val (.word w)))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 18≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤18 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→target.memory query=source.memory query) := by
  classical
  have zeroRead : eval source zeroTest=some (.val (.word (if w=0#64 then 1#64 else 0#64))) := by
    simp [eval,zeroTest,localVar,evalHOLExact,toExact,value,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have shortRead : eval source shortTest=some (.val (.word (if w.toNat<128 then 1#64 else 0#64))) := by
    simp [eval,shortTest,localVar,evalHOLExact,toExact,value,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  simp only [eval] at zeroRead shortRead
  have mapZero : source.memaddrs (panByteAlignHOL (width:=64) dst) := by simpa using mapped 0 (by decide)
  by_cases zero : w=0#64
  · obtain ⟨target,shortRun,frame,memory⟩:=short_form_execute source dst 128#64 (.const 128#64) d rfl mapZero
    have guardRun : evaluateHOLFiniteState source zeroGuard=(some (.returned (.val (.word 1#64))),target) := by
      rw [zeroGuard,evaluateHOLFiniteState_ite,zeroRead]
      simpa [zero] using shortRun
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock at clock
    refine ⟨target,1,0,by decide,by decide,by decide,?_,by simpa using frame,?_⟩
    · rw [body_shape]
      exact WitnessRadix.StateSteps.stopped_sequence source target _ _ (.returned (.val (.word 1#64))) guardRun (by omega)
    · intro query away
      exact memory query (by simpa using away 0 (by decide))
  · have zeroRun : evaluateHOLFiniteState source zeroGuard=(none,source) := by
      rw [zeroGuard,evaluateHOLFiniteState_ite,zeroRead]
      simp [zero]
    rw [body_shape,WitnessRadix.StateSteps.next_sequence source source _ _ zeroRun (Nat.le_refl _)]
    by_cases small : w.toNat<128
    · have read : eval source (localVar "w")=some (.val (.word w)) := by simp [eval,localVar,evalHOLExact,toExact,value]
      obtain ⟨target,shortRun,frame,memory⟩:=short_form_execute source dst w (localVar "w") d read mapZero
      have guardRun : evaluateHOLFiniteState source shortGuard=(some (.returned (.val (.word 1#64))),target) := by
        rw [shortGuard,evaluateHOLFiniteState_ite,shortRead]
        simpa [small] using shortRun
      have clock:=congrArg PanSemStateFiniteExact.clock frame
      change target.clock=source.clock at clock
      refine ⟨target,1,0,by decide,by decide,by decide,?_,by simpa using frame,?_⟩
      · exact WitnessRadix.StateSteps.stopped_sequence source target _ _ (.returned (.val (.word 1#64))) guardRun (by omega)
      · intro query away
        exact memory query (by simpa using away 0 (by decide))
    · have guardRun : evaluateHOLFiniteState source shortGuard=(none,source) := by
        rw [shortGuard,evaluateHOLFiniteState_ite,shortRead]
        simp [small]
      have tagRead : ∀ count≤8,eval (bind {source with clock:=source.clock-1-count} "ll" (BitVec.ofNat 64 count)) longTag=
          some (.val (.word (128#64+BitVec.ofNat 64 count))) := by
        intro count bound
        let entry:=bind {source with clock:=source.clock-1-count} "ll" (BitVec.ofNat 64 count)
        have ll : entry.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=bind_lookup_same _ _ _
        change eval entry longTag=some (.val (.word (128#64+BitVec.ofNat 64 count)))
        simp [eval,longTag,localVar,evalHOLExact,evalListHOLExact,toExact,ll,valueIsWord,valueWord,wordOpHOL,wordOp]
      obtain ⟨target,encoded,paid,lower,upper,bound,longRun,frame,memory⟩:=long_form_execute source dst w "w" longTag
        (fun count=>128#64+BitVec.ofNat 64 count) d value tagRead (by decide) (by decide) beCode putCode mapped enough
      refine ⟨target,encoded,paid,lower,upper,bound,?_,frame,memory⟩
      rw [WitnessRadix.StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)]
      exact longRun

end InitECandidate.Solver.Input.RlpWrite.WordWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.WordWrite.body_shape
#print axioms InitECandidate.Solver.Input.RlpWrite.WordWrite.execute
