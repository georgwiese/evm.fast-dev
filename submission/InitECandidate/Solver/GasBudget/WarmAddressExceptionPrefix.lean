import InitECandidate.Solver.GasBudget.WarmAddressCall
import InitECandidate.Solver.MutableTable.QueryNoException
import InitECandidate.Solver.Input.ScopedCallException

namespace InitECandidate.Solver.GasBudget.WarmAddress
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- Every escaping exception through a real warmth-query declaration
follows its actual binary normal return and bounded readonly prefix. -/
theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame query : BitVec 64)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (tableMapped : source.memaddrs (frame + 168#64))
    (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word query)])
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "is_warm_address") arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ paid answer inner, 1 ≤ paid ∧ paid ≤ Has.bodyPrice .account slots.length + 2 ∧ paid ≤ source.clock ∧
      (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name answer) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, actualArgs, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name .one (ofString "is_warm_address") arguments continuation identifier payload run
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  rw [valuesEq] at called
  obtain ⟨argument, argumentsEq, bodyEq, shapeEq, typed, queryLocal⟩ := Input.CallNormal.unary_lookup_data source.code.lookup
    (ofString "is_warm_address") (ofString "addr") .one body .one (original_code source.code installed) [.val (.word query)] actual callee shape called
  have argumentEq : argument = .val (.word query) := (List.cons.inj argumentsEq).1.symm
  rw [argumentEq] at queryLocal
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, scope⟩ := escaped
    rw [bodyEq] at bodyRun
    exact ((safe source environment installed) (callEntryStateHOLFinite source callee) rfl identifier payload (congrArg Prod.fst bodyRun)).elim
  · obtain ⟨result, inner, bodyRun, checked, tailRun, scope⟩ := continued
    rw [bodyEq] at bodyRun
    let entry := callEntryStateHOLFinite source callee
    obtain ⟨paid, answer, bounded, funded, binary, resultEq, frameFields⟩ := body_normal entry target frame query plan slots cursor floor
      (table.of_fields rfl rfl rfl rfl) (environment.of_fields rfl rfl rfl) installed ev tableMapped tableCell queryLocal queryFits queryMapped result bodyRun
    have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frameFields
    change {target with locals := source.locals} = {source with clock := source.clock - 1 - paid} at callerFrame
    have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
    rw [subtract] at callerFrame
    have canonical : Input.CallNormal.continuationEntry source target name result = bind {source with clock := source.clock - (paid + 1)} name answer := by
      rw [resultEq]
      have next := congrArg (setVarHOLFinite (ofString name) (.val (.word answer))) callerFrame
      exact next
    change paid ≤ source.clock - 1 at funded
    refine ⟨paid + 1, answer, inner, by omega, by omega, by omega, binary, ?_, scope⟩
    rw [canonical] at tailRun
    exact tailRun

end InitECandidate.Solver.GasBudget.WarmAddress

#print axioms InitECandidate.Solver.GasBudget.WarmAddress.exception_prefix
