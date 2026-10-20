import InitECandidate.Solver.Input.MainErrorTail
import InitECandidate.Solver.Input.SerializeBound
import InitECandidate.Solver.Input.SerializeEnvironment
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Input.Main.ErrorHandler
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Price the intact original SszErr handler using its actual serializer
parameters and the serializer's proved fixed return length. No successful
future serialization, output write or halt is a premise. -/
theorem handler_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out root error : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (outBinding : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (rootBinding : source.locals.lookup (ofString "z32") = some (.val (.word root)))
    (errorBinding : source.locals.lookup (ofString "err_code") = some (.val (.word error)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (outArena : AllocatedBytes.Arena out 44) (rootArena : AllocatedBytes.Arena root 32)
    (outAligned : out.toNat % 8 = 0) (rootAligned : root.toNat % 8 = 0) :
    source.clock - (evaluateHOLFiniteState source DecoderCall.handler).2.clock ≤ 51 := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (Serialize.values out root 0#64 0#64 0#64) := by
    simp [arguments,localVar,Serialize.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,outBinding,rootBinding]
  obtain ⟨callee,called,outCell,rootCell,succCell,chainCell,schemaCell⟩ := Serialize.environment source.code.lookup out root 0#64 0#64 0#64 (Serialize.original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have contract := Serialize.bound_and_return entry out root 0#64 0#64 0#64 installed outCell rootCell succCell chainCell schemaCell domain
    (outArena.weaken out 44 43 (by decide)) rootArena outAligned rootAligned
  rw [original_shape]
  apply ClockCost.scoped_reached_current source "n" .one (ofString "serialize_result") arguments (Serialize.values out root 0#64 0#64 0#64) Serialize.body tail callee .one 5 45 args called contract.1
  intro target returned run shapePass
  obtain ⟨rfl,rfl⟩ := contract.2 returned target run
  let ready := CallNormal.continuationEntry source (emptyLocalsHOLFinite (Serialize.post entry out root 0#64 0#64 0#64)) "n" (.val (.word 43#64))
  have outNow : ready.locals.lookup (ofString "out") = some (.val (.word out)) := by
    simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "n" ≠ ofString "out" from by decide] using outBinding
  have errorNow : ready.locals.lookup (ofString "err_code") = some (.val (.word error)) := by
    simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "n" ≠ ofString "err_code" from by decide] using errorBinding
  have lengthNow : ready.locals.lookup (ofString "n") = some (.val (.word 43#64)) := by
    simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  exact tail_cost ready out error installed outNow errorNow lengthNow domain outArena

end InitECandidate.Solver.Input.Main.ErrorHandler

#print axioms InitECandidate.Solver.Input.Main.ErrorHandler.handler_cost
