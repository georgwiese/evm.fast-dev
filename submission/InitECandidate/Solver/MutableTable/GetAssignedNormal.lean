import InitECandidate.Solver.MutableTable.GetNormalCall
import InitECandidate.Solver.Input.AssignedCallData
import InitECandidate.Solver.Input.BinaryCallData

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original getter also appears as assignment to an existing pair.
The actual normal caller supplies the real callee execution and shape checks. -/
theorem model_assigned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (cursor floor : Nat)
    (table : TableState source kind plan slots cursor floor) (environment : GasBudget.WarmKeys.Environment source)
    (query : BitVec 64) (queryFits : query.toNat + KeyHash.keySize kind < 2^64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (formals, body, pairShape))
    (name : MlS) (arguments : List (ExpHOL 64))
    (expectedArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word (cell plan .header 0)), .val (.word query)])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local, name), none)) (ofString "htab_get") arguments) = (none, post)) :
    ∃ paid flag value, 1 ≤ paid ∧ paid ≤ bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧
      (flag = 0#64 ∨ flag = 1#64) ∧
      post = setVarHOLFinite name (pair flag value) {source with clock := source.clock - paid} := by
  obtain ⟨positive, values, actual, callee, returnShape, target, returned, args, called, bodyRun, checked, postEq⟩ :=
    Input.CallNormal.local_data source post name (ofString "htab_get") arguments normal
  have valuesEq := Option.some.inj (args.symm.trans expectedArgs)
  rw [valuesEq] at called
  obtain ⟨bodyEq, shapeEq, tableLocal, keyLocal⟩ := Input.CallNormal.binary_lookup_known source.code.lookup (ofString "htab_get")
    (ofString "t") (ofString "key") .one .one body pairShape (.val (.word (cell plan .header 0))) (.val (.word query))
    actual callee returnShape (by decide) getCode called
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨paid, flag, value, bounded, funded, binary, resultEq, fields⟩ :=
    model_body_normal entry target kind plan slots cursor floor (table.of_fields rfl rfl rfl rfl)
      (environment.of_fields rfl rfl rfl) query queryFits queryMapped tableLocal keyLocal returned bodyRun
  have restored := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) fields
  change {target with locals := source.locals} = {source with clock := source.clock - 1 - paid} at restored
  change paid ≤ source.clock - 1 at funded
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  refine ⟨paid + 1, flag, value, by omega, by omega, by omega, binary, ?_⟩
  rw [postEq, resultEq, restored, subtract]

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.model_assigned_normal
