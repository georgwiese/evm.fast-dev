import InitECandidate.Solver.GasBudget.DispatchException
import InitECandidate.Solver.GasBudget.OpcodeChargeSitesException
import InitECandidate.Solver.GasBudget.OpcodeChargeInstalled
import InitECandidate.Solver.GasBudget.OpcodeChargeLift
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.OriginalExceptions

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem selected_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op)))
    (function : String) (arguments : List (ExpHOL 64)) (selected : tree.choose op = .invoke function arguments)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    evaluateHOLFiniteState source (.call (some (none, none)) (ofString function) arguments) = (some (.exception identifier payload), post) := by
  rw [body_choice source op opLocal, selected, Action.program, evaluateHOLFiniteState_seq_line780] at run
  generalize computed : evaluateHOLFiniteState source (.call (some (none, none)) (ofString function) arguments) = output at run ⊢
  obtain ⟨result, target⟩ := output
  cases result with
  | none =>
    change evaluateHOLFiniteState target (.return (.const 0#64)) = (some (.exception identifier payload), post) at run
    have returned : evaluateHOLFiniteState target (.return (.const 0#64)) =
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite target) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
    rw [returned] at run
    cases run
  | some result => exact run

/-- Actual dispatcher-body exceptions at any of the59 original charge sites.
The selected original helper, its real execution and its caller clock are
derived. Prefix events and terminal effects are lifted to the real dispatcher
state, including dynamically supplied DUP/SWAP/etc arguments. -/
theorem charge_site_exception (kind : OpcodeChargeSites.Kind)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used op : BitVec 64)
    (arguments : List (ExpHOL 64)) (selected : tree.choose op = .invoke kind.label arguments)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op)))
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 2#64) ∧ sp.toNat + 1 ≤ kind.names.length ∧
      StackPop.PrefixEffect source post frame (sp.toNat + 2) ∧ post.memory (frame + 16#64) = .word 0#64) ∨
    (identifier = ofString "EvmErr" ∧ payload = .val (.word 4#64) ∧ kind.names.length ≤ sp.toNat ∧ gas < BitVec.ofNat 64 kind.fee ∧
      StackPop.PrefixEffect source post frame (kind.names.length + 2)) ∨
    ∃ ready inner remaining,
      OpcodeChargePrefix.ChargedEffect source ready frame sp remaining kind.names.length (BitVec.ofNat 64 kind.fee) 1 ∧
      (wordAt source.memory (frame + 184#64)).toNat < (wordAt ready.memory (frame + 184#64)).toNat ∧
      evaluateHOLFiniteState ready kind.suffix = (some (.exception identifier payload), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  have calledRun := selected_exception source post op opLocal kind.label arguments selected identifier payload run
  obtain ⟨positive, values, actualBody, callee, returnShape, target, args, called, bodyRun, postEq, fields⟩ :=
    Input.CallNormal.ignored_exception_data source post kind.name arguments identifier payload calledRun
  have code := OpcodeChargeSites.installed source.code installed kind
  have identified := Input.LocalEffects.lookup_body source.code kind.name kind.signature.1 kind.body .one code values actualBody callee returnShape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have before := StackPop.PrefixEffect.call_entry source callee frame positive
  have outerScope : emptyLocalsHOLFinite post = emptyLocalsHOLFinite target := by rw [postEq]; rfl
  rcases OpcodeChargeSites.exception kind entry target frame sp gas used
      (OriginalCodeEnvironment.stack_pop source.code installed) (OriginalCodeEnvironment.charge_gas source.code installed)
      ev spMapped spCell gasMapped usedMapped gasCell usedCell cap (shapes Input.OriginalExceptions.Kind.EvmErr) identifier payload bodyRun with
    underflow | insufficient | charged
  · obtain ⟨actualId, actualPayload, depth, effect, zeroCell⟩ := underflow
    have total := (before.trans effect).of_emptyLocals outerScope
    have paid : 1 + (sp.toNat + 1) = sp.toNat + 2 := by omega
    rw [paid] at total
    refine Or.inl ⟨actualId, actualPayload, depth, total, ?_⟩
    rw [postEq]
    exact zeroCell
  · obtain ⟨actualId, actualPayload, depth, unavailable, effect⟩ := insufficient
    have total := (before.trans effect).of_emptyLocals outerScope
    have paid : 1 + (kind.names.length + 1) = kind.names.length + 2 := by omega
    rw [paid] at total
    exact Or.inr (Or.inl ⟨actualId, actualPayload, depth, unavailable, total⟩)
  · obtain ⟨ready, inner, remaining, effect, progress, restRun, scopeEq⟩ := charged
    refine Or.inr (Or.inr ⟨ready, inner, remaining, effect.prepend before, progress, restRun, ?_⟩)
    exact outerScope.trans scopeEq

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.selected_exception
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.charge_site_exception
