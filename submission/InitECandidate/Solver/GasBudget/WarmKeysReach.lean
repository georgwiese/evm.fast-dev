import InitECandidate.Solver.GasBudget.WarmKeysProgram

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
/-- Reach the exact warming loop from the real post-MSG_GAS caller suffix.
All preceding address warm-ups and both table constructors are traversed. -/
theorem loop_path : LocalPath "m" site RootCaller.afterMsgGas := by
  simp only [site, sites, RootCaller.afterMsgGas, RootCaller.msgGasSite, RootCaller.msgGasSites,
    RootCaller.afterSplit, RootCaller.actualSplit, RootCaller.validationContinuation, RootCaller.continuations,
    RootBudget.sites, Guest.guestFn_process_transaction, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, ↓reduceIte, List.nil_append,
    List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some]
  prove_local_path

theorem loop_safe : LocalPrefix (ofString "m") loop := by
  unfold loop loopBody setCall increment
  prove_local_prefix

/-- Actual successful original transaction execution supplies a genuine
normal run of this loop, preserving the caller's message pointer. This is
entry reachability only; its physical table/input premises are separate. -/
theorem normal_reaches_loop (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source RootCaller.afterMsgGas = (some (.returned value), post)) :
    ∃ ready warmed finish : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState ready loop = (none, warmed) ∧
      evaluateHOLFiniteState warmed afterLoop = (some (.returned value), finish) ∧
      ready.locals.lookup (ofString "m") = source.locals.lookup (ofString "m") ∧
      warmed.locals.lookup (ofString "m") = source.locals.lookup (ofString "m") ∧
      ready.code = source.code ∧ ready.eshapes = source.eshapes := by
  obtain ⟨ready, finish, siteRun, localEq, codes, shapes⟩ := loop_path.normal_reaches source post value run
  rw [site_shape] at siteRun
  obtain ⟨warmed, loopRun, restRun, sameLocal⟩ := loop_safe.normal_continue ready finish afterLoop value siteRun
  exact ⟨ready, warmed, finish, loopRun, restRun, localEq, sameLocal.trans localEq, codes, shapes⟩

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.loop_path
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.loop_safe
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.normal_reaches_loop
