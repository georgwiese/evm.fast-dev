import InitECandidate.Solver.Input.PayloadOffsetsNormal

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def extraLength : ExpHOL 64 := .op .sub [localVar "o_txs",localVar "o_extra"]
def extraTest : ExpHOL 64 := .cmp .lower (.const 32#64) extraLength
def extraGuard : ProgHOL 64 := .ite extraTest (.call (some (none,none)) (ofString "ssz_fail") [.const 51#64]) .skip
def afterExtra : ProgHOL 64 := dropLeading 1 offsetContinuation

theorem extra_shape : offsetContinuation=.seq extraGuard afterExtra := by
  simp only [offsetContinuation,offsetBody,dropLeading,afterGuard,body,Scalar.payloadBody,Guest.Software.guestFn_decode_payload,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,afterExtra,extraGuard,extraTest,extraLength,localVar]

theorem extra_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (e : source.locals.lookup (ofString "o_extra")=some (.val (.word 540#64)))
    (t : source.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))))
    (lower : 540≤(offsetWords input 1).toNat) :
    eval source extraTest=some (.val (.word (if 32<(offsetWords input 1).toNat-540 then 1#64 else 0#64))) := by
  classical
  have subtraction : (offsetWords input 1-540#64).toNat=(offsetWords input 1).toNat-540 :=
    BitVec.toNat_sub_of_le (show 540#64≤offsetWords input 1 from lower)
  simp [eval,extraTest,extraLength,localVar,evalHOLExact,evalListHOLExact,toExact,e,t,valueIsWord,valueWord,
    wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,subtraction]

/-- Actual normal continuation proves the extra-data slice is at most32 bytes;
its genuine SszErr51 rejection cannot resume the payload body. -/
theorem extra_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (e : source.locals.lookup (ofString "o_extra")=some (.val (.word 540#64)))
    (t : source.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))))
    (lower : 540≤(offsetWords input 1).toNat)
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source offsetContinuation=(some (.returned value),post)) :
    (offsetWords input 1).toNat-540≤32 ∧ evaluateHOLFiniteState source afterExtra=(some (.returned value),post) := by
  have test:=extra_test_read source input e t lower
  have guarded:=Header.test_guard_execute source extraTest 51#64 (32<(offsetWords input 1).toNat-540) test failCode exceptionShape enough
  change evaluateHOLFiniteState source extraGuard=_ at guarded
  rw [extra_shape] at run
  by_cases bad : 32<(offsetWords input 1).toNat-540
  · simp only [if_pos bad] at guarded
    have stopped:=WitnessRadix.StateSteps.stopped_sequence source _ extraGuard afterExtra _ guarded (by change source.clock-1≤source.clock; omega)
    rw [stopped] at run
    have impossible:=congrArg Prod.fst run
    cases impossible
  · simp only [if_neg bad] at guarded
    rw [WitnessRadix.StateSteps.next_sequence source source extraGuard afterExtra guarded (Nat.le_refl _)] at run
    exact ⟨by omega,run⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.extra_shape
#print axioms InitECandidate.Solver.Input.Payload.extra_test_read
#print axioms InitECandidate.Solver.Input.Payload.extra_normal
