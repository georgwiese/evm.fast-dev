import InitECandidate.Solver.GasBudget.RunFramesProgram
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.GasBudget.DispatchNormal
import InitECandidate.Solver.Input.OriginalExceptions
import InitECandidate.Solver.Input.CaughtCallData
import InitECandidate.Solver.Input.UnaryCallData
import InitECandidate.Solver.Input.ByteExpressionBound

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def opcodeArgument : ExpHOL 64 := .loadByte (.op .add [frameLoad 48#64, localVar "pc"])
def opcodeHandler : ProgHOL 64 := .call (some (none, none)) (ofString "frame_exception") [localVar "err"]
def caughtDispatch : ProgHOL 64 := .call (some (none, some (ofString "EvmErr", ofString "err", opcodeHandler)))
  (ofString "op_dispatch") [opcodeArgument]

theorem opcode_shape : opcodeBranch = .dec (ofString "err") .one (.const 0#64) caughtDispatch := by
  simp only [opcodeBranch, pcBranch, dispatchBranch, head, loopBody, RootExit.runBody, Guest.guestFn_run_frames,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some,
    caughtDispatch, opcodeArgument, opcodeHandler, frameLoad, frameAddress, localVar]

/-- Actual dispatcher or caught-handler executions, with a genuinely read
opcode byte and the actual finite callee environment. -/
def CaughtDispatchCases (source post : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  1 ≤ source.clock ∧ ∃ (op : BitVec 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)),
    op.toNat < 256 ∧ eval source opcodeArgument = some (.val (.word op)) ∧
    callee.lookup (ofString "op") = some (.val (.word op)) ∧
    ((∃ target, evaluateHOLFiniteState (callEntryStateHOLFinite source callee) OpcodeDispatch.body =
          (some (.returned (.val (.word 0#64))), target) ∧ post = {target with locals := source.locals}) ∨
     ∃ target err, evaluateHOLFiniteState (callEntryStateHOLFinite source callee) OpcodeDispatch.body =
          (some (.exception (ofString "EvmErr") (.val (.word err))), target) ∧
       evaluateHOLFiniteState (setVarHOLFinite (ofString "err") (.val (.word err)) {target with locals := source.locals}) opcodeHandler =
          (none, post))

/-- The original code/shape environments suffice; arguments, actual opcode,
callee execution, funding and handler execution all come from the real call. -/
theorem caught_dispatch_cases (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (normal : evaluateHOLFiniteState source caughtDispatch = (none, post)) : CaughtDispatchCases source post := by
  have code := OriginalCodeEnvironment.op_dispatch source.code installed
  have exceptionShape := shapes Input.OriginalExceptions.Kind.EvmErr
  obtain ⟨positive, values, actualBody, callee, actualShape, args, called, cases⟩ :=
    Input.CallNormal.ignored_caught_data source post (ofString "op_dispatch") [opcodeArgument] (ofString "EvmErr") (ofString "err") opcodeHandler exceptionShape normal
  obtain ⟨value, valuesEq, bodyEq, shapeEq, typed, binding⟩ := Input.CallNormal.unary_lookup_data source.code.lookup (ofString "op_dispatch")
    (ofString "op") .one OpcodeDispatch.body .one code values actualBody callee actualShape called
  rw [valuesEq] at args
  have read := Input.single_argument source opcodeArgument value args
  obtain ⟨op, valueEq, bounded⟩ := Input.byte_expression_value source _ value read
  rw [valueEq] at read binding
  rw [bodyEq, shapeEq] at cases
  refine ⟨positive, op, callee, bounded, read, binding, ?_⟩
  rcases cases with returned | caught
  · obtain ⟨target, returned, run, checked, postEq⟩ := returned
    have returnedEq := (OpcodeDispatch.normal_helper (callEntryStateHOLFinite source callee) target op binding returned run).1
    rw [returnedEq] at run
    exact Or.inl ⟨target, run, postEq⟩
  · exact Or.inr caught

theorem opcode_branch_cases (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (normal : evaluateHOLFiniteState source opcodeBranch = (none, post)) :
    ∃ inner, CaughtDispatchCases (bind source "err" 0#64) inner ∧ post = restore source "err" inner := by
  let entered := bind source "err" 0#64
  let output := evaluateHOLFiniteState entered caughtDispatch
  have actual := Input.ScalarScope.declare_execute source output.2 "err" (.const 0#64) 0#64 caughtDispatch output.1 rfl rfl
  rw [opcode_shape, actual] at normal
  have resultEq := congrArg Prod.fst normal
  have bodyRun : evaluateHOLFiniteState entered caughtDispatch = (none, output.2) := Prod.ext resultEq rfl
  have postEq := congrArg Prod.snd normal
  exact ⟨output.2, caught_dispatch_cases entered output.2 installed shapes bodyRun, postEq.symm⟩

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.opcode_shape
#print axioms InitECandidate.Solver.GasBudget.RunFrames.caught_dispatch_cases
#print axioms InitECandidate.Solver.GasBudget.RunFrames.opcode_branch_cases
