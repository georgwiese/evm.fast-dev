import InitECandidate.Solver.MutableTable.GetNoException
import InitECandidate.Solver.Input.ScopedCallException
import InitECandidate.Solver.Input.BinaryCallData

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem model_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (formals, body, pairShape))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "htab_get") arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ paid flag value inner, 1 ≤ paid ∧ paid ≤ bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (pair flag value) {source with clock := source.clock - paid}) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, returnShape, target, actualArgs, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name pairShape (ofString "htab_get") arguments continuation identifier payload run
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  rw [valuesEq] at called
  obtain ⟨bodyEq, shapeEq, tableLocal, keyLocal⟩ := Input.CallNormal.binary_lookup_known source.code.lookup (ofString "htab_get")
    (ofString "t") (ofString "key") .one .one body pairShape (.val (.word (cell plan .header 0))) (.val (.word query))
    actual callee returnShape (by decide) getCode called
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, scope⟩ := escaped
    rw [bodyEq] at bodyRun
    exact ((safe source.code environment.hashCode environment.memeqCode environment.findCode)
      (callEntryStateHOLFinite source callee) rfl identifier payload (congrArg Prod.fst bodyRun)).elim
  · obtain ⟨result, inner, bodyRun, checked, tailRun, scope⟩ := continued
    rw [bodyEq] at bodyRun
    let entry := callEntryStateHOLFinite source callee
    obtain ⟨paid, flag, value, bounded, funded, binary, resultEq, fields⟩ :=
      model_body_normal entry target kind plan slots cursor floor (table.of_fields rfl rfl rfl rfl)
        (environment.of_fields rfl rfl rfl) query queryFits queryMapped tableLocal keyLocal result bodyRun
    have restored := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) fields
    change {target with locals := source.locals} = {source with clock := source.clock - 1 - paid} at restored
    have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
    rw [subtract] at restored
    have canonical : Input.CallNormal.continuationEntry source target name result =
        setVarHOLFinite (ofString name) (pair flag value) {source with clock := source.clock - (paid + 1)} := by
      rw [resultEq]
      exact congrArg (setVarHOLFinite (ofString name) (pair flag value)) restored
    change paid ≤ source.clock - 1 at funded
    refine ⟨paid + 1, flag, value, inner, by omega, by omega, by omega, binary, ?_, scope⟩
    rw [canonical] at tailRun
    exact tailRun

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.model_exception_prefix
