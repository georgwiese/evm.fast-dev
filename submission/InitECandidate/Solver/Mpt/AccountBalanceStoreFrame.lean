import InitECandidate.Solver.Mpt.AccountDecodeOutput
import InitECandidate.Solver.Input.NoneControl
import InitECandidate.Solver.Input.ScalarNormal
import InitECandidate.Solver.Rlp.SliceArrayModel
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def balancePosition (payload index : BitVec 64) : BitVec 64 := payload-1#64-index
def balanceDestination (out payload index : BitVec 64) : BitVec 64 := out+(8#64+((balancePosition payload index >>> (3 : Nat))*8#64))

theorem balance_destination_span (out payload index : BitVec 64) (output : Output out)
    (small : payload.toNat≤32) (active : index.toNat<payload.toNat) :
    out.toNat≤(balanceDestination out payload index).toNat ∧ (balanceDestination out payload index).toNat<out.toNat+56 := by
  have first : (payload-1#64).toNat=payload.toNat-1 := BitVec.toNat_sub_of_le (by change 1≤payload.toNat; omega)
  have position : (balancePosition payload index).toNat=payload.toNat-1-index.toNat :=
    BitVec.toNat_sub_of_le (by change index.toNat≤(payload-1#64).toNat; rw [first]; omega) |>.trans (by rw [first])
  have positionBound : (balancePosition payload index).toNat≤31 := by omega
  have shift : (balancePosition payload index >>> (3 : Nat)).toNat=(balancePosition payload index).toNat/8 := by
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have product : ((balancePosition payload index >>> (3 : Nat))*8#64).toNat=(balancePosition payload index).toNat/8*8 := by
    rw [BitVec.toNat_mul,shift]
    change ((balancePosition payload index).toNat/8*8)%2^64=_
    exact Nat.mod_eq_of_lt (by omega)
  have inside : (8#64+((balancePosition payload index >>> (3 : Nat))*8#64)).toNat=8+(balancePosition payload index).toNat/8*8 := by
    rw [BitVec.toNat_add_of_lt (by rw [product]; change 8+(balancePosition payload index).toNat/8*8<2^64; omega),product]
    rfl
  have number : (balanceDestination out payload index).toNat=out.toNat+8+(balancePosition payload index).toNat/8*8 := by
    unfold balanceDestination
    rw [BitVec.toNat_add_of_lt (by rw [inside]; have := output.upper; omega),inside]
    omega
  rw [number]
  omega

/-- The actual normal original balance iteration writes only one word
inside the account object. Actual expression success/mapping/write contents
are derived; no byte-read or store oracle is an entry premise. -/
theorem balance_body_window (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer header payload flag index : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (fieldCell : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (output : Output out) (small : payload.toNat≤32) (active : index.toNat<payload.toNat)
    (normal : evaluateHOLFiniteState source balanceLoopBody=(none,post)) :
    Rlp.Slices.Window source post out.toNat (out.toNat+56) := by
  have positionRead : eval source (.op .sub [.op .sub [field "f1" 2,.const 1#64],localVar "i"])=some (.val (.word (balancePosition payload index))) := by
    simp [balancePosition,field,Rlp.Item.result,eval,evalHOLExact,evalListHOLExact,localVar,toExact,fieldCell,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [balance_body_shape] at normal
  obtain ⟨posInner,posRun,posRestored⟩ := Input.declaration_none source post "pos" _ (balancePosition payload index) _ positionRead normal
  let positioned := bind source "pos" (balancePosition payload index)
  have posCell : positioned.locals.lookup (ofString "pos")=some (.val (.word (balancePosition payload index))) := bind_lookup_same _ _ _
  have positionedOut : positioned.locals.lookup (ofString "acct_out")=some (.val (.word out)) :=
    (bind_lookup_other source "pos" "acct_out" (balancePosition payload index) (by decide)).trans outputCell
  have addressRead : eval positioned (.op .add [localVar "acct_out",.const 8#64,.panop .mul [.shift .lsr (localVar "pos") (.const 3#64),.const 8#64]])=
      some (.val (.word (balanceDestination out payload index))) := by
    simp [balanceDestination,eval,evalHOLExact,evalListHOLExact,localVar,toExact,positionedOut,posCell,valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL,panOpHOL]
  obtain ⟨lpInner,lpRun,lpRestored⟩ := Input.declaration_none positioned posInner "lp" _ (balanceDestination out payload index) _ addressRead posRun
  let addressed := bind positioned "lp" (balanceDestination out payload index)
  obtain ⟨middle,storeRun,incrementRun⟩ := Input.sequence_none addressed lpInner balanceStore increment lpRun
  have lpCell : addressed.locals.lookup (ofString "lp")=some (.val (.word (balanceDestination out payload index))) := bind_lookup_same _ _ _
  have lpRead : eval addressed (localVar "lp")=some (.val (.word (balanceDestination out payload index))) := by
    simp [eval,localVar,evalHOLExact,toExact,lpCell]
  obtain ⟨value,memory,read,stores,storeFrame⟩ := Input.store_at_normal addressed middle (localVar "lp") _ (balanceDestination out payload index) lpRead storeRun
  have scalar := Input.op_length addressed .or _ value read
  have assigned := Input.LocalEffects.assign middle.code (ofString "i") (.op .add [localVar "i",.const 1#64]) middle rfl
  change Input.LocalEffects.erase (evaluateHOLFiniteState middle increment).2=Input.LocalEffects.erase middle at assigned
  rw [incrementRun] at assigned
  have incrementMemory := Input.LocalEffects.memory_of_erase middle lpInner assigned
  obtain ⟨lower,upper⟩ := balance_destination_span out payload index output small active
  intro query outside
  rw [posRestored,lpRestored]
  change lpInner.memory query=source.memory query
  rw [incrementMemory,storeFrame]
  apply Input.words_away (flattenHOL value) (balanceDestination out payload index) query addressed.memaddrs addressed.memory memory stores
  intro item inside
  have indexZero : item=0 := by rw [scalar] at inside; omega
  subst item
  simp only [Nat.mul_zero,BitVec.add_zero]
  intro same
  have number := congrArg BitVec.toNat same
  rcases outside with before|after <;> omega

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_destination_span
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_body_window
