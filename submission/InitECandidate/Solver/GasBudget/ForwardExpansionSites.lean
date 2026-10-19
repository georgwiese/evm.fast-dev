import InitECandidate.Solver.GasBudget.ForwardExpansion
import InitECandidate.Solver.GasBudget.ForwardCalculatorSites

namespace InitECandidate.Solver.GasBudget.ForwardPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def eraseExpansionContinuation : ProgHOL 64 → ProgHOL 64
  | .decCall name shape function arguments (.seq charge (.seq debit (.seq expansion _))) =>
      .decCall name shape function arguments (.seq charge (.seq debit (.seq expansion .skip)))
  | _ => .skip
def selectedExpansion (declaration : Decl (BitVec 64)) : ProgHOL 64 :=
  match declaration with
  | .function fn => eraseExpansionContinuation (((calculatorSites (progToHOL fn.body))[0]?).getD .skip)
  | _ => .skip

set_option maxRecDepth 10000 in
/-- The actual memory expansion immediately follows the checked calculator,
charge and debit sequence in all four unchanged CALL opcodes. -/
theorem opcode_expansion_sites :
    selectedExpansion Guest.guestFn_op_call = expansionProgram (calculatorArgumentsFor (WitnessRadix.QueryBranch.localVar "value")) .skip ∧
    selectedExpansion Guest.guestFn_op_callcode = expansionProgram (calculatorArgumentsFor (WitnessRadix.QueryBranch.localVar "value")) .skip ∧
    selectedExpansion Guest.guestFn_op_delegatecall = expansionProgram (calculatorArgumentsFor (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64])) .skip ∧
    selectedExpansion Guest.guestFn_op_staticcall = expansionProgram (calculatorArgumentsFor (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64])) .skip := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [selectedExpansion, Guest.guestFn_op_call, Guest.guestFn_op_callcode, Guest.guestFn_op_delegatecall, Guest.guestFn_op_staticcall,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some, calculatorSites,
    ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, List.getElem?_cons_zero, Option.getD_some, eraseExpansionContinuation]
  all_goals rfl

end InitECandidate.Solver.GasBudget.ForwardPrefix

#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.opcode_expansion_sites
