import InitECandidate.Solver.MutableTable.FindGeneralStep
import InitECandidate.Solver.MutableTable.MemeqAnyCall
import InitECandidate.Solver.MutableTable.MemeqAnyFast32
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.ScopedNoLoopControl
import InitECandidate.Solver.Input.LocalEffectsScoped
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_equal_quiet (code) : Input.ClockCost.Bound code afterEqual 0 := by
  apply Input.ClockCost.of_quiet
  exact Input.QuietClock.sequence code _ _
    (Input.QuietClock.conditional code _ _ _ (Input.QuietClock.returned code _) (Input.QuietClock.skip code))
    (Input.QuietClock.assign code _ _)

/-- One real original probe body has a fixed cost without a mapping or
readability premise for either comparison operand. Invalid reads stop early. -/
theorem any_step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (locals : Locals source p index) (keyLength : p.keyLength=32#64)
    (code : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one)) :
    source.clock-(evaluateHOLFiniteState source loopBody).2.clock≤5 := by
  obtain ⟨callee,called,aCell,bCell,nCell⟩ := MemeqByteRuntime.environment source.code.lookup (p.keys+index*p.stride) p.key 32 code
  have args:=general_comparison_arguments source p index .word locals keyLength
  exact Input.ClockCost.scoped_current source (ofString "eq") .one (ofString "memeq") comparisonArguments _ Memeq32.body afterEqual callee .one 4 0 args called
    (MemeqAny.tight_body_cost (callEntryStateHOLFinite source callee) nCell) (after_equal_quiet source.code)

/-- The actual comparator and the caller's tests/update change only locals
and clock on every outcome. No successful comparison is supplied. -/
theorem any_step_readonly (code)
    (installed : code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one)) : Input.LocalEffects.Preserves code loopBody := by
  apply Input.LocalEffects.scoped_body code (ofString "eq") .one (ofString "memeq") comparisonArguments afterEqual Memeq32.formals Memeq32.body .one installed (MemeqAny.readonly code)
  exact Input.LocalEffects.sequence code _ _
    (Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.returned code _) (Input.LocalEffects.skip code))
    (Input.LocalEffects.assign code _ _)

theorem after_equal_no_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source afterEqual).1≠some .break ∧ (evaluateHOLFiniteState source afterEqual).1≠some .continue := by
  have first : Input.PureDecision (.ite equalTest (.return (localVar "i")) .skip) := .ite _ (.returned _) .skip
  have info:=first.summary source
  rw [afterEqual,evaluateHOLFiniteState_seq_line780]
  generalize run : evaluateHOLFiniteState source (.ite equalTest (.return (localVar "i")) .skip)=output at info
  obtain ⟨result,target⟩ := output
  cases result with
  | none => exact ((Input.LocalPrefix.assign (key:=ofString "n") (ofString "i") nextIndex (by decide)).summary_full target).2.2
  | some result => exact info.2

theorem any_step_no_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source loopBody).1≠some .break ∧ (evaluateHOLFiniteState source loopBody).1≠some .continue :=
  Input.scoped_no_loop_control (ofString "eq") .one (ofString "memeq") comparisonArguments afterEqual after_equal_no_control source

/-- Genuine fallthrough proves the exact masked next index and restores
every other real loop local, regardless of comparison-read failures. -/
theorem any_step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (locals : Locals source p index) (keyLength : p.keyLength=32#64)
    (code : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (normal : evaluateHOLFiniteState source loopBody=(none,post)) : Locals post p (next p index) := by
  obtain ⟨callee,called,aCell,bCell,nCell⟩ := MemeqByteRuntime.environment source.code.lookup (p.keys+index*p.stride) p.key 32 code
  have args:=general_comparison_arguments source p index .word locals keyLength
  obtain ⟨funded,target,value,inner,bodyRun,checked,remaining,endpoint⟩ := Input.CallNormal.scoped_none source post "eq" .one (ofString "memeq") comparisonArguments _ Memeq32.body afterEqual callee .one args called normal
  let current:=Input.CallNormal.continuationEntry source target "eq" value
  have currentLocals : Locals current p index :=
    ⟨(Input.CallNormal.continuation_lookup_other source target "eq" "cap" value (by decide)).trans locals.cap,
      (Input.CallNormal.continuation_lookup_other source target "eq" "klen" value (by decide)).trans locals.klen,
      (Input.CallNormal.continuation_lookup_other source target "eq" "stride" value (by decide)).trans locals.stride,
      (Input.CallNormal.continuation_lookup_other source target "eq" "keys" value (by decide)).trans locals.keys,
      (Input.CallNormal.continuation_lookup_other source target "eq" "used" value (by decide)).trans locals.used,
      (Input.CallNormal.continuation_lookup_other source target "eq" "key" value (by decide)).trans locals.key,
      (Input.CallNormal.continuation_lookup_other source target "eq" "i" value (by decide)).trans locals.index⟩
  obtain ⟨middle,guardRun,assignRun⟩ := Input.sequence_none current inner _ _ remaining
  have decision : Input.PureDecision (.ite equalTest (.return (localVar "i")) .skip) := .ite _ (.returned _) .skip
  have info:=decision.summary current
  rw [guardRun] at info
  have same : middle=current := info.1 rfl
  subst middle
  have read:=next_read current p index currentLocals
  have updated:=StateSteps.assign_execute current "i" nextIndex index (next p index) currentLocals.index read
  have innerEq : inner=bind current "i" (next p index) := (congrArg Prod.snd (assignRun.symm.trans updated))
  rw [endpoint,innerEq]
  exact ⟨(restore_lookup_other source _ "eq" "cap" (by decide)).trans ((bind_lookup_other current "i" "cap" _ (by decide)).trans currentLocals.cap),
    (restore_lookup_other source _ "eq" "klen" (by decide)).trans ((bind_lookup_other current "i" "klen" _ (by decide)).trans currentLocals.klen),
    (restore_lookup_other source _ "eq" "stride" (by decide)).trans ((bind_lookup_other current "i" "stride" _ (by decide)).trans currentLocals.stride),
    (restore_lookup_other source _ "eq" "keys" (by decide)).trans ((bind_lookup_other current "i" "keys" _ (by decide)).trans currentLocals.keys),
    (restore_lookup_other source _ "eq" "used" (by decide)).trans ((bind_lookup_other current "i" "used" _ (by decide)).trans currentLocals.used),
    (restore_lookup_other source _ "eq" "key" (by decide)).trans ((bind_lookup_other current "i" "key" _ (by decide)).trans currentLocals.key),
    (restore_lookup_other source _ "eq" "i" (by decide)).trans (bind_lookup_same current "i" _)⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.after_equal_quiet
#print axioms InitECandidate.Solver.MutableTable.Find.any_step_cost
#print axioms InitECandidate.Solver.MutableTable.Find.any_step_readonly
#print axioms InitECandidate.Solver.MutableTable.Find.after_equal_no_control
#print axioms InitECandidate.Solver.MutableTable.Find.any_step_no_control
#print axioms InitECandidate.Solver.MutableTable.Find.any_step_normal
