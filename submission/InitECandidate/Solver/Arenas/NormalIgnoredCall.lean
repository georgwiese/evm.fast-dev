import InitECandidate.Solver.Arenas.Normal
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.UnaryCallData

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual ignored arena allocation, as used in memory growth, derives its
reached room and one caller clock and exports the exact full cursor update. -/
theorem ignored_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (direction : Direction) (pointer limit amount : BitVec 64)
    (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word amount)])
    (code : source.code.lookup (ofString (functionName direction)) = some (formals, body direction, .one))
    (trapInstalled : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (pointerGlobal : source.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString (limitName direction)) = some (.val (.word limit)))
    (ordered : Ordered direction pointer limit) (aligned : limit.toNat % 8 = 0)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString (functionName direction)) arguments) = (none, target)) :
    Room direction pointer limit amount ∧ 1 ≤ source.clock ∧ target = post {source with clock := source.clock - 1} direction pointer amount := by
  obtain ⟨positive, values, actual, callee, shape, calleePost, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source target (ofString (functionName direction)) arguments normal
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨argument, argumentsEq, bodyEq, shapeEq, typed, binding⟩ :=
    Input.CallNormal.unary_lookup_data source.code.lookup (ofString (functionName direction)) (ofString "n") .one (body direction) .one
      code [.val (.word amount)] actual callee shape called
  have argumentEq : argument = .val (.word amount) := (List.cons.inj argumentsEq).1.symm
  rw [argumentEq] at binding
  rw [bodyEq] at bodyRun
  obtain ⟨room, valueEq, frame⟩ := post_of_normal (callEntryStateHOLFinite source callee) calleePost direction pointer limit amount binding
    pointerGlobal limitGlobal ordered aligned trapInstalled returned bodyRun
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  change {calleePost with locals := source.locals} = post {source with clock := source.clock - 1} direction pointer amount at callerFrame
  exact ⟨room, positive, postEq.trans callerFrame⟩

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.ignored_normal
