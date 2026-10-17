import InitECandidate.Solver.GasBudget.ValueFee

namespace InitECandidate.Solver.GasBudget.ValueFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def sites : ProgHOL 64→List (ProgHOL 64)
  | code@(.decCall name _ function _ rest)=>
      (if name=ofString "need" ∧ function=ofString "add_sat" then [code] else [])++sites rest
  | .seq first second | .ite _ first second=>sites first++sites second
  | .dec _ _ _ rest | .while _ rest=>sites rest
  | _=>[]
def eraseContinuation : ProgHOL 64→ProgHOL 64
  | .decCall name shape function arguments (.seq first _)=>.decCall name shape function arguments (.seq first .skip)
  | _=>.skip
def selectedSite (declaration : Decl (BitVec 64)) : ProgHOL 64 :=
  match declaration with
  | .function fn=>eraseContinuation (((sites (progToHOL fn.body))[0]?).getD .skip)
  | _=>.skip
def selectedValue (declaration : Decl (BitVec 64)) : ExpHOL 64 :=
  match declaration with
  | .function fn=>(((((ForwardPrefix.calculatorArguments (progToHOL fn.body))[0]?).getD [])[0]?).getD (.const 0#64))
  | _=>.const 0#64

set_option maxRecDepth 10000 in
theorem opcode_fee_sites : selectedSite Guest.guestFn_op_call=program .skip ∧ selectedSite Guest.guestFn_op_callcode=program .skip := by
  constructor
  all_goals simp only [selectedSite,Guest.guestFn_op_call,Guest.guestFn_op_callcode,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,sites,↓reduceIte,List.nil_append,List.cons_append,List.append_nil,
    List.getElem?_cons_zero,Option.getD_some,eraseContinuation]
  all_goals rfl

set_option maxRecDepth 10000 in
theorem opcode_zero_values : selectedValue Guest.guestFn_op_delegatecall=.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64] ∧
    selectedValue Guest.guestFn_op_staticcall=.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64] := by
  constructor
  all_goals simp only [selectedValue,Guest.guestFn_op_delegatecall,Guest.guestFn_op_staticcall,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,ForwardPrefix.calculatorArguments,↓reduceIte,
    List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some]
  all_goals rfl

theorem zero_stipend : CallGas.stipend (fun _=>0#64)=0#64 := by
  simp [CallGas.stipend,U256Zero.resultWord,U256Zero.mixed]

end InitECandidate.Solver.GasBudget.ValueFee

#print axioms InitECandidate.Solver.GasBudget.ValueFee.opcode_fee_sites
#print axioms InitECandidate.Solver.GasBudget.ValueFee.opcode_zero_values
#print axioms InitECandidate.Solver.GasBudget.ValueFee.zero_stipend
