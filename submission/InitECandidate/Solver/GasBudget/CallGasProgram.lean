import InitECandidate.Solver.GasBudget.U256Zero

namespace InitECandidate.Solver.GasBudget.CallGas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_calculate_message_call_gas with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "value",Input.RlpWrite.U256Value.tupleShape),(ofString "gas",.one),
  (ofString "gas_left",.one),(ofString "memory_cost",.one),(ofString "extra_gas",.one)]
def returnShape : ShapeHOL := .comb [.one,.one]
def pair (debit forwarded : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word debit),.val (.word forwarded)]
def returnAmounts : ProgHOL 64 := .return (.rstruct [.op .add [localVar "g",localVar "extra_gas"],.op .add [localVar "g",localVar "stipend"]])
def clamp : ProgHOL 64 := .ite (.cmp .lower (localVar "mx") (localVar "g")) (.assign .local (ofString "g") (localVar "mx")) .skip
def afterG : ProgHOL 64 := .seq clamp returnAmounts
def capExpression : ExpHOL 64 := .op .sub [localVar "avail",.shift .lsr (localVar "avail") (.const 6#64)]
def afterAvail : ProgHOL 64 := .dec (ofString "mx") .one capExpression (.dec (ofString "g") .one (localVar "gas") afterG)
def availableExpression : ExpHOL 64 := .op .sub [.op .sub [localVar "gas_left",localVar "memory_cost"],localVar "extra_gas"]
def shortage : ProgHOL 64 := .decCall (ofString "c") .one (ofString "add_sat") [localVar "gas",localVar "extra_gas"]
  (.decCall (ofString "s") .one (ofString "add_sat") [localVar "gas",localVar "stipend"] (.return (.rstruct [localVar "c",localVar "s"])))
def afterNeed : ProgHOL 64 := .seq (.ite (.cmp .lower (localVar "gas_left") (localVar "need")) shortage .skip)
  (.dec (ofString "avail") .one availableExpression afterAvail)
def afterStipend : ProgHOL 64 := .decCall (ofString "need") .one (ofString "add_sat") [localVar "extra_gas",localVar "memory_cost"] afterNeed
def stipendUpdate : ProgHOL 64 := .ite (.cmp .equal (localVar "vz") (.const 0#64)) (.assign .local (ofString "stipend") (.const 2300#64)) .skip
def afterZero : ProgHOL 64 := .dec (ofString "stipend") .one (.const 0#64) (.seq stipendUpdate afterStipend)

theorem body_shape : body=.decCall (ofString "vz") .one (ofString "u256_is_zero") [localVar "value"] afterZero := by
  simp only [body,Guest.guestFn_calculate_message_call_gas,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    afterZero,stipendUpdate,afterStipend,afterNeed,shortage,availableExpression,afterAvail,capExpression,afterG,clamp,returnAmounts,localVar]

def cap (left : BitVec 64) : BitVec 64 := left-(left >>> (6:Nat))
def capped (requested left : BitVec 64) : BitVec 64 := if cap left<requested then cap left else requested
def stipend (words : U256Zero.Quad) : BitVec 64 := if U256Zero.resultWord words=0#64 then 2300#64 else 0#64

theorem cap_number (left : BitVec 64) : (cap left).toNat=left.toNat-left.toNat/64 ∧ (cap left).toNat≤left.toNat := by
  have shiftNumber : (left >>> (6:Nat)).toNat=left.toNat/64 := by rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have shiftSmall : left >>> (6:Nat)≤left := by change (left >>> (6:Nat)).toNat≤left.toNat; rw [shiftNumber]; exact Nat.div_le_self _ _
  rw [cap,BitVec.toNat_sub_of_le shiftSmall,shiftNumber]
  exact ⟨rfl,Nat.sub_le _ _⟩

theorem capped_number (requested left : BitVec 64) : (capped requested left).toNat=min requested.toNat (cap left).toNat ∧ (capped requested left).toNat≤left.toNat := by
  have number : (capped requested left).toNat=min requested.toNat (cap left).toNat := by
    by_cases less : cap left<requested
    · simp only [capped,if_pos less,Nat.min_eq_right (Nat.le_of_lt (show (cap left).toNat<requested.toNat from less))]
    · simp only [capped,if_neg less,Nat.min_eq_left (show requested.toNat≤(cap left).toNat from by change ¬(cap left).toNat<requested.toNat at less; omega)]
  exact ⟨number,by rw [number]; exact (Nat.min_le_right _ _).trans (cap_number left).2⟩

theorem stipend_bound (words : U256Zero.Quad) : (stipend words).toNat≤2300 := by
  unfold stipend
  split <;> decide

end InitECandidate.Solver.GasBudget.CallGas

#print axioms InitECandidate.Solver.GasBudget.CallGas.body_shape
#print axioms InitECandidate.Solver.GasBudget.CallGas.cap_number
#print axioms InitECandidate.Solver.GasBudget.CallGas.capped_number
#print axioms InitECandidate.Solver.GasBudget.CallGas.stipend_bound
