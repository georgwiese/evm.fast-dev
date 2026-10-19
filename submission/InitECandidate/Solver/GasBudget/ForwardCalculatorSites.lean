import InitECandidate.Solver.GasBudget.ForwardCalculator
import InitECandidate.Solver.GasBudget.ForwardSites

namespace InitECandidate.Solver.GasBudget.ForwardPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def calculatorSites : ProgHOL 64 → List (ProgHOL 64)
  | code@(.decCall _ _ function _ rest) =>
      (if function = ofString "calculate_message_call_gas" then [code] else []) ++ calculatorSites rest
  | .seq first second | .ite _ first second => calculatorSites first ++ calculatorSites second
  | .dec _ _ _ rest | .while _ rest => calculatorSites rest
  | _ => []
def eraseCalculatorContinuation : ProgHOL 64 → ProgHOL 64
  | .decCall name shape function arguments rest => .decCall name shape function arguments (eraseContinuation rest)
  | _ => .skip
def selectedCalculator (declaration : Decl (BitVec 64)) : ProgHOL 64 :=
  match declaration with
  | .function fn => eraseCalculatorContinuation (((calculatorSites (progToHOL fn.body))[0]?).getD .skip)
  | _ => .skip
def calculatorArgumentsFor (value : ExpHOL 64) : List (ExpHOL 64) :=
  [value, localVar "gw", frameLoad 64#64, .const 0#64, .const 0#64]

set_option maxRecDepth 10000 in
/-- The calculator and actual forward debit are adjacent literal syntax in
all four unchanged opcodes; only the later continuation is abstracted. -/
theorem opcode_calculator_sites :
    selectedCalculator Guest.guestFn_op_call = calculatorProgram (calculatorArgumentsFor (localVar "value")) .skip ∧
    selectedCalculator Guest.guestFn_op_callcode = calculatorProgram (calculatorArgumentsFor (localVar "value")) .skip ∧
    selectedCalculator Guest.guestFn_op_delegatecall = calculatorProgram (calculatorArgumentsFor (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64])) .skip ∧
    selectedCalculator Guest.guestFn_op_staticcall = calculatorProgram (calculatorArgumentsFor (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64])) .skip := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [selectedCalculator, Guest.guestFn_op_call, Guest.guestFn_op_callcode, Guest.guestFn_op_delegatecall, Guest.guestFn_op_staticcall,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some, calculatorSites,
    ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some,
    eraseCalculatorContinuation, eraseContinuation]
  all_goals rfl

end InitECandidate.Solver.GasBudget.ForwardPrefix

#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.opcode_calculator_sites
