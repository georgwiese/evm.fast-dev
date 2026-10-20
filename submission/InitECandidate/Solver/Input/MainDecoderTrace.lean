import InitECandidate.Solver.Input.MainDecoderBodyTrace
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The literal original decoder on all actual non-timeout paths, including
the earliest schema/length errors. The only input premise beyond host size
is the challenge's declared gas bound; actual records belong to this poststate. -/
theorem decoder_trace (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (bounded : input.length%2^64≤Guest.maxInputBytes)
    (gas : Guest.GasLimit.declaredGasLimit input≤200000000)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Header.body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(input.length%2^64)/4+witnessLength input/2+522 ∧
      ((∃ error : BitVec 64,result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨
       (result=some (.returned (.val (.word (RequestPrefix.cursor input)))) ∧ WitnessDecoded input post)) := by
  by_cases rejects : Rejects input
  · let padded := {source with clock:=source.clock+1}
    have ready : Environment input padded := ⟨environment.pointer,environment.length,environment.bytes,environment.offsets,environment.heap,environment.scalars,
      environment.code,environment.shapes,environment.domain,environment.shared,environment.little,environment.oracle,environment.host⟩
    have rejected := rejected_body input padded ready rejects (by change 1≤source.clock+1; omega)
    have actual := panPropsEvaluateAddClockEq Header.body source result post 1 ⟨run,notTimeout⟩
    have equality := rejected.symm.trans actual
    have answer := congrArg Prod.fst equality
    have clock := congrArg (fun output => output.2.clock) equality
    change source.clock+1-1=post.clock+1 at clock
    exact ⟨by omega,Or.inl ⟨rejectionCode input,answer.symm⟩⟩
  · exact decoder_body_trace input source post environment bounded rejects gas result run notTimeout

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.decoder_trace
