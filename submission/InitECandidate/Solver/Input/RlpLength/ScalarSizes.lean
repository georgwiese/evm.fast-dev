import InitECandidate.Solver.Input.RlpLength.ShortOrBe

namespace InitECandidate.Solver.Input.RlpLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

namespace Header

def encodedLength (value : BitVec 64) : Nat:=if value.toNat≤55 then 1 else Be.byteCount 8 value+1
def body : ProgHOL 64 := match Guest.guestFn_rlp_header_len with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "n",.one)]
def condition : ExpHOL 64 := .cmp .notLower (.const 55#64) (localVar "n")
theorem body_shape : body=.seq (shortGuard condition) (longTail "n") := by
  simp only [body,Guest.guestFn_rlp_header_len,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    shortGuard,condition,longTail,returnOnePlus,localVar]

theorem execute_exact (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (n : source.locals.lookup (ofString "n")=some (.val (.word value)))
    (code : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 9≤source.clock) :
    ∃ target encoded paid,encoded=encodedLength value ∧ 1≤encoded ∧ encoded≤9 ∧ paid≤9 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  have test : eval source condition=some (.val (.word (if value.toNat≤55 then 1#64 else 0#64))) := by
    simp [eval,condition,localVar,evalHOLExact,toExact,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def]
  rw [body_shape]
  exact short_or_be_exact source "n" value n condition (value.toNat≤55) test code enough

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (n : source.locals.lookup (ofString "n")=some (.val (.word value)))
    (code : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 9≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤9 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  obtain ⟨target,encoded,paid,_exactCount,lower,upper,bounded,run,frame⟩:=execute_exact source value n code enough
  exact ⟨target,encoded,paid,lower,upper,bounded,run,frame⟩

theorem call_execute_exact (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word value)])
    (code : source.code.lookup (ofString "rlp_header_len")=some (formals,body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 10≤source.clock) :
    ∃ encoded paid,encoded=encodedLength value ∧ 1≤encoded ∧ encoded≤9 ∧ paid≤9 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_header_len") expressions continuation)=
        let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2) := by
  obtain ⟨callee,called,n⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_header_len") "n" body value code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,exactCount,lower,upper,bound,bodyRun,frame⟩:=execute_exact entry value n beCode (by change 9≤source.clock-1; omega)
  exact ⟨encoded,paid,exactCount,lower,upper,bound,CallNormal.pure_return_execute source target name (ofString "rlp_header_len") expressions [.val (.word value)]
    body continuation callee (BitVec.ofNat 64 encoded) paid args called (by omega) bodyRun frame⟩
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word value)])
    (code : source.code.lookup (ofString "rlp_header_len")=some (formals,body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 10≤source.clock) :
    ∃ encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤9 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_header_len") expressions continuation)=
        let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2) := by
  obtain ⟨encoded,paid,_exactCount,lower,upper,bounded,run⟩:=call_execute_exact source value name expressions continuation args code beCode enough
  exact ⟨encoded,paid,lower,upper,bounded,run⟩

end Header

namespace WordSize
def body : ProgHOL 64 := match Guest.guestFn_rlp_word_encoded_len with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "w",.one)]
def condition : ExpHOL 64 := .cmp .lower (localVar "w") (.const 128#64)
theorem body_shape : body=.seq (shortGuard condition) (longTail "w") := by
  simp only [body,Guest.guestFn_rlp_word_encoded_len,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    shortGuard,condition,longTail,returnOnePlus,localVar]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (w : source.locals.lookup (ofString "w")=some (.val (.word value)))
    (code : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 9≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤9 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  have test : eval source condition=some (.val (.word (if value.toNat<128 then 1#64 else 0#64))) := by
    simp [eval,condition,localVar,evalHOLExact,toExact,w,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  rw [body_shape]
  exact short_or_be source "w" value w condition (value.toNat<128) test code enough

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word value)])
    (code : source.code.lookup (ofString "rlp_word_encoded_len")=some (formals,body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 10≤source.clock) :
    ∃ encoded paid,1≤encoded ∧ encoded≤9 ∧ paid≤9 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_word_encoded_len") expressions continuation)=
        let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-paid} name (BitVec.ofNat 64 encoded)) continuation
        (output.1,restore source name output.2) := by
  obtain ⟨callee,called,w⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_word_encoded_len") "w" body value code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,encoded,paid,lower,upper,bound,bodyRun,frame⟩:=execute entry value w beCode (by change 9≤source.clock-1; omega)
  exact ⟨encoded,paid,lower,upper,bound,CallNormal.pure_return_execute source target name (ofString "rlp_word_encoded_len") expressions [.val (.word value)]
    body continuation callee (BitVec.ofNat 64 encoded) paid args called (by omega) bodyRun frame⟩
end WordSize

end InitECandidate.Solver.Input.RlpLength

#print axioms InitECandidate.Solver.Input.RlpLength.Header.execute
#print axioms InitECandidate.Solver.Input.RlpLength.Header.call_execute
#print axioms InitECandidate.Solver.Input.RlpLength.WordSize.execute
#print axioms InitECandidate.Solver.Input.RlpLength.WordSize.call_execute

#print axioms InitECandidate.Solver.Input.RlpLength.Header.execute_exact
#print axioms InitECandidate.Solver.Input.RlpLength.Header.call_execute_exact
