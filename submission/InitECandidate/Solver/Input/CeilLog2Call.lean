import InitECandidate.Solver.Input.CeilLog2Body
import InitECandidate.Solver.Input.PureReturn
import InitECandidate.Solver.Input.TerminatingPaddedScopeArgs

namespace InitECandidate.Solver.Input.CeilLog2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real original call derives its own funding and returned exponent
from the observed non-timeout continuation, at any actual clock budget. -/
theorem call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (n : BitVec 64) (depth : Nat)
    (small : depth<64) (bounded : n.toNat≤2^depth) (name : String)
    (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word n)])
    (code : source.code.lookup (ofString "ceil_log2")=some (formals,body,.one))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "ceil_log2") expressions continuation)=(result,post))
    (notTimeout : result≠some .timeOut) :
    ∃ next innerPost exponent,exponent≤depth ∧ n.toNat≤2^exponent ∧ (0<exponent→2^(exponent-1)<n.toNat) ∧
      2^exponent≤max 1 (2*n.toNat) ∧ exponent+1≤source.clock ∧
      next.locals=source.locals.update (ofString name,.val (.word (BitVec.ofNat 64 exponent))) ∧
      next.clock=source.clock-(exponent+1) ∧ frozen next=frozen source ∧
      evaluateHOLFiniteState next continuation=(result,innerPost) ∧ post=restore source name innerPost := by
  obtain ⟨callee,called,nLocal⟩ := CallNormal.unary_environment source.code.lookup (ofString "ceil_log2") "n" body n code
  let padded := callEntryStateHOLFinite {source with clock:=source.clock+(depth+1)} callee
  obtain ⟨middle,exponent,exponentBound,ceiling,previous,bodyRun,clock,frame⟩ := body_execute padded n depth small bounded (by change depth≤source.clock+(depth+1)-1; omega) nLocal
  have shapePass : (shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 exponent)))) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 exponent)))) .one)=true := by simp [shapeOfHOLExact,shapeEqHOL]
  obtain ⟨funded,positive,lowered,innerPost,remaining,restored⟩ := terminating_padded_scope_args source post middle name .one (ofString "ceil_log2") expressions [.val (.word n)]
    body continuation callee .one (.val (.word (BitVec.ofNat 64 exponent))) (depth+1) args called (by omega) bodyRun shapePass result run notTimeout
  let next := CallNormal.continuationEntry source {middle with clock:=middle.clock-(depth+1)} name (.val (.word (BitVec.ofNat 64 exponent)))
  have clockEq : middle.clock=source.clock+(depth+1)-1-exponent := clock
  have paid : exponent+1≤source.clock := by omega
  have nextClock : next.clock=source.clock-(exponent+1) := by change middle.clock-(depth+1)=_; omega
  exact ⟨next,innerPost,exponent,exponentBound,ceiling,previous,(ceiling_size _ _ ceiling previous).2,paid,rfl,nextClock,frame,remaining,restored⟩

end InitECandidate.Solver.Input.CeilLog2

#print axioms InitECandidate.Solver.Input.CeilLog2.call_trace
