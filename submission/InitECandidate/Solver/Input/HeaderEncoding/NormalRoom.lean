import InitECandidate.Solver.Input.HeaderEncoding.FirstWideFrontier
import InitECandidate.Solver.Input.RlpWrite.U256NormalRoom
import InitECandidate.Solver.Input.AssignedCallActual
import InitECandidate.Solver.Input.CallPrefixCommand

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def afterFirstWide : ProgHOL 64:=.seq advance (fields (baseRest.drop 7) afterBase)

theorem from_wide_shape : fromWide=.seq (call (.wide 64)) afterFirstWide := rfl

/-- A normal original encoder necessarily allocated both its1024-byte
output and the first wide writer's32-byte temporary. The stronger room
used by its complete normal contract is therefore a conclusion. -/
theorem normal_room (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤33806089496)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    buffer.toNat+1056≤33806089496 := by
  obtain ⟨current,inner,room,code,cell,endpoint,remaining⟩:=before_wide_frontier source post buffer installed heap bounded value normal
  rw [from_wide_shape] at remaining
  have never : NoReturn.Never (CallPrefix.program [.command (call (.wide 64))] .skip):=
    NoReturn.sequence _ _ (field_never _) NoReturn.skip
  obtain ⟨after,afterInner,firstTrace,firstEndpoint,rest⟩:=CallPrefix.normal_trace current inner
    [.command (call (.wide 64))] afterFirstWide value never remaining
  obtain ⟨afterCall,callRun,next⟩:=firstTrace.command_next (call (.wide 64)) []
  obtain ⟨values,actualBody,callee,shape,childTarget,returned,args,called,childRun⟩:=CallNormal.assigned_actual current afterCall
    (some (.local,ofString "w")) (ofString "rlp_put_u256") (arguments (.wide 64)) callRun
  have installedCurrent : OriginalCode.Installed current.code:=by rw [code]; exact installed
  have bodyEq:=GlobalEffects.lookup_body current.code (ofString "rlp_put_u256") RlpWrite.U256Put.formals RlpWrite.U256Put.body .one
    (OriginalRlp.rlp_put_u256 current.code installedCurrent) values actualBody callee shape called
  subst actualBody
  have growth:=PersistentAlloc.guards buffer 1024#64 room
  have temporaryRoom:=RlpWrite.U256Put.normal_room (callEntryStateHOLFinite current callee) childTarget
    (PersistentAlloc.rounded buffer 1024#64) installedCurrent cell growth.2.2.2.1 returned childRun
  have grows:=growth.2.2.1
  change buffer.toNat+1024≤(PersistentAlloc.rounded buffer 1024#64).toNat at grows
  omega

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.from_wide_shape
#print axioms InitECandidate.Solver.Input.HeaderEncoding.normal_room
