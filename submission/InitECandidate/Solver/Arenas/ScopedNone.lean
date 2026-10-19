import InitECandidate.Solver.Arenas.Cost
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real continuing allocation derives request room and its exact cursor,
returned pointer and continuation. No future allocation success/funding is
supplied, and the original trap routine excludes a false continuation. -/
theorem scoped_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (direction : Direction)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer limit amount : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word amount)])
    (pointerGlobal : source.globals.lookup (ofString (pointerName direction))=some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString (limitName direction))=some (.val (.word limit)))
    (ordered : Ordered direction pointer limit) (aligned : limit.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString (functionName direction)) arguments continuation)=(none,target)) :
    Room direction pointer limit amount ∧ 1≤source.clock ∧ ∃ inner,
      evaluateHOLFiniteState (bind (post {source with clock := source.clock-1} direction pointer amount) name (resultWord direction pointer amount)) continuation=(none,inner) ∧
      target=restore source name inner := by
  have code := original_code source.code installed direction
  obtain ⟨callee,called,amountLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString (functionName direction)) "n" (body direction) amount code
  obtain ⟨positive,calleePost,returned,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_none source target name .one (ofString (functionName direction)) arguments _ (body direction) continuation callee .one args called normal
  have room := room_of_normal (callEntryStateHOLFinite source callee) calleePost direction pointer limit amount amountLocal pointerGlobal limitGlobal ordered
    (Input.Trap.original_code source.code installed) returned bodyRun
  have actual := call_execute source direction name arguments continuation pointer limit amount args code pointerGlobal limitGlobal aligned room positive
  have joined := actual.symm.trans normal
  let ready := bind (post {source with clock := source.clock-1} direction pointer amount) name (resultWord direction pointer amount)
  have resultEq := congrArg Prod.fst joined
  change (evaluateHOLFiniteState ready continuation).1=none at resultEq
  have stateEq := (congrArg Prod.snd joined).symm
  change target=restore source name (evaluateHOLFiniteState ready continuation).2 at stateEq
  exact ⟨room,positive,(evaluateHOLFiniteState ready continuation).2,Prod.ext resultEq rfl,stateEq⟩

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.scoped_none
