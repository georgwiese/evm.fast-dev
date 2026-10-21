import InitECandidate.Solver.Input.RequestsHashBodyCost

namespace InitECandidate.Solver.Input.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (rq out : BitVec 64) : List (ValueHOL 64) := [.val (.word rq),.val (.word out)]
def rawLocals (rq out : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "out" then some (.val (.word out)) else if name=ofString "rq" then some (.val (.word rq)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (rq out : BitVec 64)
    (code : codeFn (ofString "htr_requests")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htr_requests") (values rq out)=some (body,callee,.one) ∧
      callee.lookup (ofString "rq")=some (.val (.word rq)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values rq out).length ∧
      ((formals.zip (values rq out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "htr_requests") (values rq out)=some (body,rawLocals rq out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "rq"≠ofString "out" from by decide],by rw [locals]; simp [rawLocals]⟩

def price (counts : Kind→Nat) := 1827*counts .deposit+988*counts .wdreq+1364*counts .cons+1652*counts .bdep+813*counts .bexit+145844

/-- Original two-word request-hash caller includes its genuine caller tick,
all five actual request counts, final container and both heap scopes. Every
observed non-timeout failure remains covered; no numerical ceiling is used. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros) (image : Image source rq pointers counts)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : Geometry rq ch (ch+160#64) pointers counts capacity) (separation : Separation rq stp accel chunk)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values rq out))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_requests") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤price counts+1 := by
  obtain ⟨callee,called,rqLocal,outLocal⟩ := environment source.code.lookup rq out (original_code source.code workspace.sha.installed)
  have calleeImage : Image (callEntryStateHOLFinite source callee) rq pointers counts := ⟨image.fields⟩
  exact ClockCost.call_current_terminating source post destination (ofString "htr_requests") arguments (values rq out) body callee .one (price counts) args called
    (fun result target actual notTimeout=>body_cost (callEntryStateHOLFinite source callee) target rq ch out stp accel chunk zeros pointers counts capacity
      (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) rqLocal outLocal calleeImage heap geometry separation result actual notTimeout)
    result run notTimeout

end InitECandidate.Solver.Input.RequestsHash

#print axioms InitECandidate.Solver.Input.RequestsHash.environment
#print axioms InitECandidate.Solver.Input.RequestsHash.call_cost
