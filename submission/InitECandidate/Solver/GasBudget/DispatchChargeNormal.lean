import InitECandidate.Solver.GasBudget.DispatchNormal
import InitECandidate.Solver.GasBudget.OpcodeChargeInstalled
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual normal dispatcher execution at any original literal-charge site
reaches the genuine suffix after positive gas credit. The helper and its
dynamic arguments, code/return and both caller/prefix clocks are derived. -/
theorem charge_site_normal (kind : OpcodeChargeSites.Kind)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame op : BitVec 64)
    (arguments : List (ExpHOL 64)) (selected : tree.choose op = .invoke kind.label arguments)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op)))
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    value = .val (.word 0#64) ∧ ∃ ready inner returned,
      kind.names.length + 2 ≤ source.clock ∧ ready.clock = source.clock - (kind.names.length + 2) ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - (kind.names.length + 2)} ∧
      evaluateHOLFiniteState ready kind.suffix = (some (.returned returned), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + kind.fee ∧
      (wordAt source.memory (frame + 184#64)).toNat < (wordAt ready.memory (frame + 184#64)).toNat ∧
      (wordAt ready.memory (frame + 16#64)).toNat + kind.names.length = (wordAt source.memory (frame + 16#64)).toNat ∧
      ∀ address, address ≠ frame + 16#64 → address ≠ frame + 64#64 → address ≠ frame + 184#64 → ready.memory address = source.memory address := by
  obtain ⟨zero, function, actualArguments, middle, actualSelected, helperRun, postEq⟩ := normal_helper source post op opLocal value run
  rw [selected] at actualSelected
  cases actualSelected
  obtain ⟨positive, values, actualBody, callee, returnShape, target, returned, args, called, bodyRun, checked, middleEq, fields⟩ :=
    Input.CallNormal.ignored_data source middle kind.name arguments helperRun
  have code := OpcodeChargeSites.installed source.code installed kind
  have identified := Input.LocalEffects.lookup_body source.code kind.name kind.signature.1 kind.body .one code values actualBody callee returnShape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨ready, inner, fits, clock, frameEq, suffixRun, scopeEq, budget, credit, progress, depth, outside⟩ :=
    OpcodeChargeSites.normal kind entry target frame (OriginalCodeEnvironment.stack_pop source.code installed)
      (OriginalCodeEnvironment.charge_gas source.code installed) ev cap returned bodyRun
  change kind.names.length + 1 ≤ source.clock - 1 at fits
  have totalFits : kind.names.length + 2 ≤ source.clock := by omega
  have subtract : source.clock - 1 - (kind.names.length + 1) = source.clock - (kind.names.length + 2) := by omega
  change ready.clock = source.clock - 1 - (kind.names.length + 1) at clock
  change emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - 1 - (kind.names.length + 1)} at frameEq
  rw [subtract] at clock frameEq
  refine ⟨zero, ready, inner, returned, totalFits, clock, frameEq, suffixRun, ?_, budget, credit, progress, depth, outside⟩
  rw [postEq, middleEq]
  exact scopeEq

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.charge_site_normal
