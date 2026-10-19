import InitECandidate.Solver.GasBudget.RevertProgram
import InitECandidate.Solver.Input.NoReturnScoped
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.GasBudget.RevertOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem never_returns : Input.NoReturn.Never body := by
  simp only [body, Guest.guestFn_op_revert, progToHOL]
  repeat first
    | apply Input.NoReturn.scoped_call
    | exact Input.NoReturn.raised_sequence _ _ _
    | apply Input.NoReturn.sequence
    | exact Input.NoReturn.ignored_call _ _
    | exact Input.NoReturn.store _ _

theorem call_not_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code)
    (run : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_revert") []) = (none, post)) : False := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "op_revert") [] run
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "op_revert") [] body .one
    (original_code source.code installed) values actual callee shape called
  rw [bodyEq] at bodyRun
  exact never_returns (callEntryStateHOLFinite source callee) returned (congrArg Prod.fst bodyRun)

end InitECandidate.Solver.GasBudget.RevertOpcode

#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.never_returns
#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.call_not_normal
