import InitECandidate.Solver.GasBudget.AddressMaskedCall
import InitECandidate.Solver.GasBudget.AddressMaskedNoException
import InitECandidate.Solver.Input.ScopedCallException

namespace InitECandidate.Solver.GasBudget.AddressMasked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite MemoryWriter

theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (words : U256Value.Words)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : BytesMapped source (frame + 240#64) 20)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) expressions = some [U256Value.tuple words])
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "to_address_masked") expressions continuation) = (some (.exception identifier payload), post)) :
    ∃ paid memory inner, paid ≤ 8 ∧ paid ≤ source.clock ∧
      evaluateHOLFiniteState (bind {source with memory := memory, clock := source.clock - paid} name (frame + 240#64)) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner ∧
      (∀ query, BytesAway (frame + 240#64) query 20 → memory query = source.memory query) := by
  obtain ⟨positive, values, actual, callee, shape, target, actualArgs, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name .one (ofString "to_address_masked") expressions continuation identifier payload run
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  rw [valuesEq] at called
  obtain ⟨value, valuesEq, bodyEq, shapeEq, typed, binding⟩ := Input.CallNormal.unary_lookup_data source.code.lookup
    (ofString "to_address_masked") (ofString "v") U256Value.tupleShape body .one (original_code source.code installed) [U256Value.tuple words] actual callee shape called
  have valueEq : value = U256Value.tuple words := (List.cons.inj valuesEq).1.symm
  rw [valueEq] at binding
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, scope⟩ := escaped
    rw [bodyEq] at bodyRun
    exact ((safe source.code installed) (callEntryStateHOLFinite source callee) rfl identifier payload (congrArg Prod.fst bodyRun)).elim
  · obtain ⟨result, inner, bodyRun, checked, tailRun, scope⟩ := continued
    rw [bodyEq] at bodyRun
    obtain ⟨resultEq, paid, bounded, funded, clock, fields, away⟩ := body_normal (callEntryStateHOLFinite source callee) target frame words installed ev binding mapped result bodyRun
    have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals, clock := target.clock}) fields
    change {target with locals := source.locals} = {source with memory := target.memory, clock := target.clock} at callerFrame
    change target.clock = source.clock - 1 - paid at clock
    have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
    have canonical : Input.CallNormal.continuationEntry source target name result =
        bind {source with memory := target.memory, clock := source.clock - (paid + 1)} name (frame + 240#64) := by
      rw [resultEq]
      have next := congrArg (setVarHOLFinite (ofString name) (.val (.word (frame + 240#64)))) callerFrame
      change Input.CallNormal.continuationEntry source target name (.val (.word (frame + 240#64))) =
        bind {source with memory := target.memory, clock := target.clock} name (frame + 240#64) at next
      rw [clock, subtract] at next
      exact next
    change paid ≤ source.clock - 1 at funded
    refine ⟨paid + 1, target.memory, inner, by omega, by omega, ?_, scope, away⟩
    rw [canonical] at tailRun
    exact tailRun

end InitECandidate.Solver.GasBudget.AddressMasked

#print axioms InitECandidate.Solver.GasBudget.AddressMasked.exception_prefix
