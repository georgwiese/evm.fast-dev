import InitECandidate.Solver.Input.UDivMod.Built
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual divisor-nonzero call, ABI/shape checks, tuple binding and eventual
lexical restoration. The body costs0or64 clocks, plus the real call clock. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (nonzero : b≠0#64) (enough : 65≤source.clock) (name : String)
    (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (values a b))
    (code : source.code.lookup (ofString "udivmod")=some (formals,body,returnShape)) :
    ∃ next q r paid,paid≤64 ∧
      next.locals=source.locals.update (ofString name,pairValue q r) ∧
      next.clock=source.clock-1-paid ∧ frozen next=frozen source ∧
      (b.toNat≤2^63→q.toNat=a.toNat/b.toNat ∧ r.toNat=a.toNat%b.toNat) ∧
      evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "udivmod") expressions continuation)=
        let output:=evaluateHOLFiniteState next continuation
        (output.1,restore source name output.2) := by
  classical
  obtain ⟨callee,called,aLocal,bLocal⟩:=environment source.code.lookup a b code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,q,r,paid,bound,bodyRun,clock,frame,arithmetic⟩:=body_execute_nonzero entry a b aLocal bLocal nonzero (by change 64≤source.clock-1; omega)
  have shapePass : (shapeEqHOL (shapeOfHOLExact (pairValue q r)) returnShape && shapeEqHOL (shapeOfHOLExact (pairValue q r)) returnShape)=true := by
    simp [pairValue,returnShape,shapeOfHOLExact,shapeEqHOL_eq_true]
  have actual:=CallNormal.return_execute source target name returnShape (ofString "udivmod") expressions (values a b) body continuation callee returnShape
    (pairValue q r) args called (by omega) bodyRun shapePass
  let next:=CallNormal.continuationEntry source target name (pairValue q r)
  refine ⟨next,q,r,paid,bound,rfl,clock,?_,arithmetic,actual⟩
  change frozen target=frozen source
  exact frame

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.call_execute
