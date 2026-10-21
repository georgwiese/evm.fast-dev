import InitECandidate.Solver.Arenas.Cost
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every real scoped arena allocation either stops within its caller/trap
allowance or supplies actual room and its exact updated caller state. -/
theorem scoped_trace (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (direction : Direction) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (pointer limit amount : BitVec 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word amount)])
    (installed : Input.OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString (pointerName direction))=some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString (limitName direction))=some (.val (.word limit)))
    (ordered : Ordered direction pointer limit) (aligned : limit.toNat%8=0)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString (functionName direction)) arguments continuation)=(result,target)) :
    source.clock-target.clock≤2 ∨
      1≤source.clock ∧ Room direction pointer limit amount ∧ ∃ inner,
        evaluateHOLFiniteState (bind (post {source with clock:=source.clock-1} direction pointer amount) name (resultWord direction pointer amount)) continuation=(result,inner) ∧
        target=restore source name inner := by
  obtain ⟨callee,called,amountCell⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString (functionName direction)) "n" (body direction) amount (original_code source.code installed direction)
  have price:=body_price source.code installed direction (callEntryStateHOLFinite source callee) rfl
  rcases Input.CallNormal.scoped_trace source target name .one (ofString (functionName direction)) arguments _ (body direction) continuation callee .one 1 args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨parsed,answer,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨room,valueEq,frame⟩:=post_of_normal (callEntryStateHOLFinite source callee) parsed direction pointer limit amount amountCell
      pointerGlobal limitGlobal ordered aligned (Input.Trap.original_code source.code installed) answer bodyRun
    rw [valueEq] at continued
    have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
    change {parsed with locals:=source.locals}=post {source with clock:=source.clock-1} direction pointer amount at callerFrame
    change evaluateHOLFiniteState (bind {parsed with locals:=source.locals} name (resultWord direction pointer amount)) continuation=(result,inner) at continued
    rw [callerFrame] at continued
    exact Or.inr ⟨funded,room,inner,continued,endpoint⟩

/-- A genuine normal scoped return derives its own allocation room and
funding before exposing the exact continuation and lexical restoration. -/
theorem scoped_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (direction : Direction) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (pointer limit amount : BitVec 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word amount)])
    (installed : Input.OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString (pointerName direction))=some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString (limitName direction))=some (.val (.word limit)))
    (ordered : Ordered direction pointer limit) (aligned : limit.toNat%8=0)
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString (functionName direction)) arguments continuation)=(some (.returned returned),target)) :
    1≤source.clock ∧ Room direction pointer limit amount ∧ ∃ inner,
      evaluateHOLFiniteState (bind (post {source with clock:=source.clock-1} direction pointer amount) name (resultWord direction pointer amount)) continuation=(some (.returned returned),inner) ∧
      target=restore source name inner := by
  obtain ⟨callee,called,amountCell⟩:=Input.CallNormal.unary_environment source.code.lookup (ofString (functionName direction)) "n" (body direction) amount (original_code source.code installed direction)
  obtain ⟨funded,parsed,answer,inner,bodyRun,checked,continued,endpoint⟩:=
    Input.CallNormal.scoped_normal source target name .one (ofString (functionName direction)) arguments _ (body direction) continuation callee .one args called returned run
  obtain ⟨room,valueEq,frame⟩:=post_of_normal (callEntryStateHOLFinite source callee) parsed direction pointer limit amount amountCell
    pointerGlobal limitGlobal ordered aligned (Input.Trap.original_code source.code installed) answer bodyRun
  rw [valueEq] at continued
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  change {parsed with locals:=source.locals}=post {source with clock:=source.clock-1} direction pointer amount at callerFrame
  change evaluateHOLFiniteState (bind {parsed with locals:=source.locals} name (resultWord direction pointer amount)) continuation=(some (.returned returned),inner) at continued
  rw [callerFrame] at continued
  exact ⟨funded,room,inner,continued,endpoint⟩

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.scoped_trace
#print axioms InitECandidate.Solver.Arenas.scoped_normal
