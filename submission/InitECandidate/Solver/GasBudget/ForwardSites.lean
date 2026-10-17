import InitECandidate.Solver.GasBudget.ForwardPrefix

namespace InitECandidate.Solver.GasBudget.ForwardPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def sites : ProgHOL 64→List (ProgHOL 64)
  | code@(.seq (.call (some (none,none)) function [.rfield 0 (.var .local name)]) rest)=>
      (if function=ofString "charge_gas" ∧ name=ofString "mcg" then [code] else [])++sites rest
  | .seq first second | .ite _ first second=>sites first++sites second
  | .dec _ _ _ rest | .decCall _ _ _ _ rest | .while _ rest=>sites rest
  | _=>[]
def eraseContinuation : ProgHOL 64→ProgHOL 64
  | .seq first (.seq second _)=>.seq first (.seq second .skip)
  | _=>.skip
def selectedSite (declaration : Decl (BitVec 64)) : ProgHOL 64 :=
  match declaration with
  | .function fn=>eraseContinuation (((sites (progToHOL fn.body))[0]?).getD .skip)
  | _=>.skip

def calculatorArguments : ProgHOL 64→List (List (ExpHOL 64))
  | .decCall _ _ function arguments rest=>
      (if function=ofString "calculate_message_call_gas" then [arguments] else [])++calculatorArguments rest
  | .seq first second | .ite _ first second=>calculatorArguments first++calculatorArguments second
  | .dec _ _ _ rest | .while _ rest=>calculatorArguments rest
  | _=>[]
def selectedCosts (declaration : Decl (BitVec 64)) : List (ExpHOL 64) :=
  match declaration with
  | .function fn=>((((calculatorArguments (progToHOL fn.body))[0]?).getD []).drop 3)
  | _=>[]

set_option maxRecDepth 10000 in
/-- The checked charge/counter-debit sequence is a literal subtree of each of
the four fixed call opcodes. Only the following continuation is abstracted. -/
theorem opcode_sites : selectedSite Guest.guestFn_op_call=program .skip ∧
    selectedSite Guest.guestFn_op_callcode=program .skip ∧
    selectedSite Guest.guestFn_op_delegatecall=program .skip ∧
    selectedSite Guest.guestFn_op_staticcall=program .skip := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals simp only [selectedSite,Guest.guestFn_op_call,Guest.guestFn_op_callcode,Guest.guestFn_op_delegatecall,Guest.guestFn_op_staticcall,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,sites,
    ↓reduceIte,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some,eraseContinuation]
  all_goals rfl

set_option maxRecDepth 10000 in
/-- Each fixed opcode supplies exactly zero memory and extra cost to the
calculator, the concrete mode in which its complete body/caller was checked. -/
theorem opcode_zero_costs : selectedCosts Guest.guestFn_op_call=[.const 0#64,.const 0#64] ∧
    selectedCosts Guest.guestFn_op_callcode=[.const 0#64,.const 0#64] ∧
    selectedCosts Guest.guestFn_op_delegatecall=[.const 0#64,.const 0#64] ∧
    selectedCosts Guest.guestFn_op_staticcall=[.const 0#64,.const 0#64] := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals simp only [selectedCosts,Guest.guestFn_op_call,Guest.guestFn_op_callcode,Guest.guestFn_op_delegatecall,Guest.guestFn_op_staticcall,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,calculatorArguments,
    ↓reduceIte,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some]
  all_goals rfl

end InitECandidate.Solver.GasBudget.ForwardPrefix

#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.opcode_sites
#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.opcode_zero_costs
