import InitECandidate.Solver.Input.RlpWrite.U256MinLoop

namespace InitECandidate.Solver.Input.RlpWrite.U256Min
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete actual minimal-U256 writer, including its real byte-length call,
whole loop, return and both lexical scopes. Actual stores stay in32 bytes. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (dst : BitVec 64)
    (a : source.locals.lookup (ofString "a")=some (U256Value.tuple words))
    (outLocal : source.locals.lookup (ofString "out")=some (.val (.word dst)))
    (byteCode : source.code.lookup (ofString "u256_byte_length")=some (U256ByteLength.formals,U256ByteLength.body,.one))
    (bitsCode : source.code.lookup (ofString "u256_bit_length")=some (U256Bits.formals,U256Bits.body,.one))
    (bitCode : source.code.lookup (ofString "bit_length64")=some (BitLength.formals,BitLength.body,.one))
    (limbCode : source.code.lookup (ofString "u256_limb")=some (U256Limb.formals,U256Limb.body,.one))
    (mapped : ∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 offset))) (enough : 67≤source.clock) :
    ∃ target length paid,length≤32 ∧ paid≤67 ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 length)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      (∀ query,(∀ offset<32,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 offset))→target.memory query=source.memory query) := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "a"]=some [U256Value.tuple words] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,a]
  obtain ⟨length,bound,called⟩:=U256ByteLength.call_execute source words "len" [localVar "a"] afterLength args byteCode bitsCode bitCode (by omega)
  let entered:=bind {source with clock:=source.clock-1-2} "len" (BitVec.ofNat 64 length)
  let si:=bind entered "i" 0#64
  have aI : si.locals.lookup (ofString "a")=some (U256Value.tuple words):=
    (bind_lookup_other _ "i" "a" _ (by decide)).trans ((bind_lookup_other _ "len" "a" _ (by decide)).trans a)
  have outI : si.locals.lookup (ofString "out")=some (.val (.word dst)):=
    (bind_lookup_other _ "i" "out" _ (by decide)).trans ((bind_lookup_other _ "len" "out" _ (by decide)).trans outLocal)
  have iI : si.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 0))):=bind_lookup_same _ _ _
  have nI : si.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other _ "i" "len" _ (by decide)).trans (bind_lookup_same _ _ _)
  obtain ⟨next,loopRun,frame,finalI,others,memory⟩:=loop_execute si words dst 0 length length (by omega) bound aI outI iI nI limbCode
    (by intro offset inside; exact mapped offset (by omega)) (by change 2*length≤source.clock-1-2; omega)
  have nextClock:=congrArg PanSemStateFiniteExact.clock frame
  change next.clock=source.clock-1-2-2*length at nextClock
  have nNext : next.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))):=
    (others "len" (by decide)).trans nI
  have returnRun : evaluateHOLFiniteState next (.return (localVar "len"))=(some (.returned (.val (.word (BitVec.ofNat 64 length)))),emptyLocalsHOLFinite next) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,nNext,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have initializedRun : evaluateHOLFiniteState si initialized=(some (.returned (.val (.word (BitVec.ofNat 64 length)))),emptyLocalsHOLFinite next) := by
    rw [initialized,WitnessRadix.StateSteps.next_sequence si next _ _ loopRun (by change next.clock≤source.clock-1-2; omega)]
    exact returnRun
  have declared:=ScalarScope.declare_execute entered _ "i" (.const 0#64) 0#64 initialized _ rfl initializedRun
  let target:=restore source "len" (restore entered "i" (emptyLocalsHOLFinite next))
  let paid:=3+2*length
  refine ⟨target,length,paid,bound,by dsimp [paid]; omega,?_,?_,?_⟩
  · rw [body_shape,called]
    exact congrArg (fun output : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>(output.1,restore source "len" output.2)) declared
  · have pureFrame:=congrArg emptyLocalsHOLFinite frame
    change emptyLocalsHOLFinite next=emptyLocalsHOLFinite {source with memory:=next.memory,clock:=source.clock-1-2-2*length} at pureFrame
    change emptyLocalsHOLFinite next=emptyLocalsHOLFinite {source with memory:=next.memory,clock:=source.clock-paid}
    have subtract : source.clock-1-2-2*length=source.clock-paid := by dsimp [paid]; omega
    simpa only [subtract] using pureFrame
  · intro query away
    exact memory query (by intro offset inside; exact away offset (by omega))

end InitECandidate.Solver.Input.RlpWrite.U256Min

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.execute
