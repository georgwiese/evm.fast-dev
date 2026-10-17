import InitECandidate.Solver.Input.RlpWrite.Forms

namespace InitECandidate.Solver.Input.RlpWrite.HeaderWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_write_header with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "dst",.one),(ofString "base",.one),(ofString "n",.one)]
def condition : ExpHOL 64 := .cmp .notLower (.const 55#64) (localVar "n")
def shortTag : ExpHOL 64 := .op .add [localVar "base",localVar "n"]
def longTag : ExpHOL 64 := .op .add [localVar "base",.const 55#64,localVar "ll"]

theorem body_shape : body=.seq (.ite condition (shortForm shortTag) .skip) (longForm "n" longTag) := by
  simp only [body,Guest.guestFn_rlp_write_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    condition,shortForm,shortTag,longForm,longTag,lengthTail,RlpLength.returnOnePlus,localVar]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst base n : BitVec 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (b : source.locals.lookup (ofString "base")=some (.val (.word base)))
    (len : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 18≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤18 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→target.memory query=source.memory query) := by
  classical
  have readTest : eval source condition=some (.val (.word (if n.toNat≤55 then 1#64 else 0#64))) := by
    simp [eval,condition,localVar,evalHOLExact,toExact,len,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def]
  simp only [eval] at readTest
  by_cases small : n.toNat≤55
  · have tagRead : eval source shortTag=some (.val (.word (base+n))) := by
      simp [eval,shortTag,localVar,evalHOLExact,evalListHOLExact,toExact,b,len,valueIsWord,valueWord,wordOpHOL,wordOp]
    have mapZero : source.memaddrs (panByteAlignHOL (width:=64) dst) := by simpa using mapped 0 (by decide)
    obtain ⟨target,shortRun,frame,memory⟩:=short_form_execute source dst (base+n) shortTag d tagRead mapZero
    have guardRun : evaluateHOLFiniteState source (.ite condition (shortForm shortTag) .skip)=
        (some (.returned (.val (.word 1#64))),target) := by
      rw [evaluateHOLFiniteState_ite,readTest]
      simpa [small] using shortRun
    have targetClock : target.clock=source.clock := by
      have clock:=congrArg PanSemStateFiniteExact.clock frame
      exact clock
    refine ⟨target,1,0,by decide,by decide,by decide,?_,by simpa using frame,?_⟩
    · rw [body_shape]
      exact WitnessRadix.StateSteps.stopped_sequence source target _ _ (.returned (.val (.word 1#64))) guardRun (by omega)
    · intro query away
      exact memory query (by simpa using away 0 (by decide))
  · have guardRun : evaluateHOLFiniteState source (.ite condition (shortForm shortTag) .skip)=(none,source) := by
      rw [evaluateHOLFiniteState_ite,readTest]
      simp [small]
    have tagRead : ∀ count≤8,eval (bind {source with clock:=source.clock-1-count} "ll" (BitVec.ofNat 64 count)) longTag=
        some (.val (.word (base+55#64+BitVec.ofNat 64 count))) := by
      intro count bound
      let entry:=bind {source with clock:=source.clock-1-count} "ll" (BitVec.ofNat 64 count)
      have ll : entry.locals.lookup (ofString "ll")=some (.val (.word (BitVec.ofNat 64 count))):=bind_lookup_same _ _ _
      have savedBase : entry.locals.lookup (ofString "base")=some (.val (.word base)):=
        (bind_lookup_other _ "ll" "base" _ (by decide)).trans b
      change eval entry longTag=some (.val (.word (base+55#64+BitVec.ofNat 64 count)))
      simp [eval,longTag,localVar,evalHOLExact,evalListHOLExact,toExact,ll,savedBase,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]
    obtain ⟨target,encoded,paid,lower,upper,bound,longRun,frame,memory⟩:=long_form_execute source dst n "n" longTag
      (fun count=>base+55#64+BitVec.ofNat 64 count) d len tagRead (by decide) (by decide) beCode putCode mapped enough
    refine ⟨target,encoded,paid,lower,upper,bound,?_,frame,memory⟩
    rw [body_shape,WitnessRadix.StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)]
    exact longRun

end InitECandidate.Solver.Input.RlpWrite.HeaderWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.HeaderWrite.body_shape
#print axioms InitECandidate.Solver.Input.RlpWrite.HeaderWrite.execute
