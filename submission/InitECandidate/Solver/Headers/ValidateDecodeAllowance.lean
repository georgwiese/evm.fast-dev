import InitECandidate.Solver.Headers.ValidateDecodeControl
import InitECandidate.Solver.Input.VarList.RecordSizes

namespace InitECandidate.Solver.Headers.Validate
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem prefix_mono (price : Nat→Nat) : Monotone (Input.VarList.sumPrefix price) := by
  intro first last inside
  induction inside with
  | refl=>rfl
  | step before ih=>simp only [Input.VarList.sumPrefix]; omega

def decodeSum (data : Data) := Input.VarList.sumPrefix (fun index=>decodePrice (data.lengths index).toNat+1)
def decodeRemaining (data : Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  decodeSum data data.count-decodeSum data (Input.CounterFlow.counterWord source (ofString "i")).toNat

theorem remaining_read (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (bounded : index≤data.count) :
    decodeRemaining data source=decodeSum data data.count-decodeSum data index := by
  have small : index<2^64 := by have h:=layout.count; omega
  have indexMod : index%18446744073709551616=index := Nat.mod_eq_of_lt small
  simp [decodeRemaining,Input.CounterFlow.counterWord,state.indexCell,valueWord,BitVec.toNat_ofNat,indexMod]

theorem remaining_step (data : Data) (index : Nat) (inside : index<data.count) :
    decodePrice (data.lengths index).toNat+1+(decodeSum data data.count-decodeSum data (index+1))=
      decodeSum data data.count-decodeSum data index := by
  have bounded:=prefix_mono (fun index=>decodePrice (data.lengths index).toNat+1) (show index+1≤data.count by omega)
  have next : decodeSum data (index+1)=decodeSum data index+(decodePrice (data.lengths index).toNat+1) := rfl
  change decodeSum data (index+1)≤decodeSum data data.count at bounded
  omega

/-- Source clock collection includes one original loop tick per row,
without charging the entire input separately for each header. -/
theorem decode_sum_formula (data : Data) (count : Nat) :
    decodeSum data count=251*Input.VarList.sumPrefix (fun index=>(data.lengths index).toNat) count+1578*count+
      20*Input.VarList.sumPrefix (fun index=>(data.lengths index).toNat/136) count := by
  induction count with
  | zero=>rfl
  | succ count ih=>
    change decodeSum data count+(decodePrice (data.lengths count).toNat+1)=_
    rw [ih]
    simp only [Input.VarList.sumPrefix,decodePrice,WitnessRadix.Keccak256.price]
    omega

theorem decode_sum_bound (data : Data) (budget : Nat)
    (bytes : Input.VarList.sumPrefix (fun index=>(data.lengths index).toNat) data.count≤budget) :
    decodeSum data data.count≤251*budget+1578*data.count+20*(budget/136) := by
  have floors (count : Nat) : 136*Input.VarList.sumPrefix (fun index=>(data.lengths index).toNat/136) count≤
      Input.VarList.sumPrefix (fun index=>(data.lengths index).toNat) count := by
    induction count with
    | zero=>rfl
    | succ count ih=>
      have individual:=Nat.div_mul_le_self (data.lengths count).toNat 136
      simp only [Input.VarList.sumPrefix]
      omega
  have fractional : Input.VarList.sumPrefix (fun index=>(data.lengths index).toNat/136) data.count≤budget/136 := by
    have whole:=floors data.count
    omega
  rw [decode_sum_formula]
  omega

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.prefix_mono
#print axioms InitECandidate.Solver.Headers.Validate.remaining_read
#print axioms InitECandidate.Solver.Headers.Validate.remaining_step
#print axioms InitECandidate.Solver.Headers.Validate.decode_sum_formula
#print axioms InitECandidate.Solver.Headers.Validate.decode_sum_bound
