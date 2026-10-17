import InitECandidate.Solver.Input.RlpLength.BlockSuffixProgram

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual two assigning header calls, total addition and return. Natural bounds
make both modular additions exact; no assumption about hash collisions is used. -/
theorem suffix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count sum total : Nat) (old : BitVec 64)
    (countSmall : count<2^31) (sumLower : 25*count≤sum) (sumUpper : sum≤57*count) (totalSmall : total≤2^32)
    (wl : source.locals.lookup (ofString "wl")=some (.val (.word (BitVec.ofNat 64 sum))))
    (t : source.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))))
    (hl : source.locals.lookup (ofString "hl")=some (.val (.word old)))
    (listCode : source.code.lookup (ofString "rlp_list_header_len")=some (ListHeader.formals,ListHeader.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 22≤source.clock) :
    ∃ target encoded paid,25*count≤encoded ∧ encoded≤total+sum+18 ∧ paid≤22 ∧
      (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source withdrawalSuffix=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "wl"]=
      some [.val (.word (BitVec.ofNat 64 sum))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,wl]
  obtain ⟨h1,p1,h1Low,h1High,p1Bound,run1⟩:=ListHeader.assign_execute source (BitVec.ofNat 64 sum) old "hl" [localVar "wl"] hl args listCode headerCode beCode (by omega)
  let s1:=bind {source with clock:=source.clock-1-p1} "hl" (BitVec.ofNat 64 h1)
  have t1 : s1.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 total))) :=
    (bind_lookup_other _ "hl" "total" _ (by decide)).trans t
  have wl1 : s1.locals.lookup (ofString "wl")=some (.val (.word (BitVec.ofNat 64 sum))) :=
    (bind_lookup_other _ "hl" "wl" _ (by decide)).trans wl
  have hl1 : s1.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 h1))):=bind_lookup_same _ _ _
  let subtotal:=total+h1+sum
  have readTotal : eval s1 addWithdrawalExpression=some (.val (.word (BitVec.ofNat 64 subtotal))) := by
    simp [eval,addWithdrawalExpression,evalHOLExact,evalListHOLExact,toExact,localVar,t1,wl1,hl1,valueIsWord,valueWord,wordOpHOL,wordOp,
      subtotal,←BitVec.ofNat_add,Nat.add_assoc]
  have assignRun:=WitnessRadix.StateSteps.assign_execute s1 "total" addWithdrawalExpression (BitVec.ofNat 64 total) (BitVec.ofNat 64 subtotal) t1 readTotal
  let s2:=bind s1 "total" (BitVec.ofNat 64 subtotal)
  have t2 : s2.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 subtotal))):=bind_lookup_same _ _ _
  have hl2 : s2.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 h1))) :=
    (bind_lookup_other _ "total" "hl" _ (by decide)).trans hl1
  have args2 : evalListHOLFinite s2 (h:=fun address=>Classical.propDecidable (s2.memaddrs address)) [localVar "total"]=
      some [.val (.word (BitVec.ofNat 64 subtotal))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,t2]
  obtain ⟨h2,p2,h2Low,h2High,p2Bound,run2⟩:=ListHeader.assign_execute s2 (BitVec.ofNat 64 subtotal) (BitVec.ofNat 64 h1) "hl" [localVar "total"] hl2 args2 listCode headerCode beCode
    (by change 11≤source.clock-1-p1; omega)
  let s3:=bind {s2 with clock:=s2.clock-1-p2} "hl" (BitVec.ofNat 64 h2)
  have t3 : s3.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 subtotal))) :=
    (bind_lookup_other _ "hl" "total" _ (by decide)).trans t2
  have hl3 : s3.locals.lookup (ofString "hl")=some (.val (.word (BitVec.ofNat 64 h2))):=bind_lookup_same _ _ _
  have returnRun : evaluateHOLFiniteState s3 lengthReturn=
      (some (.returned (.val (.word (BitVec.ofNat 64 (subtotal+h2))))),emptyLocalsHOLFinite s3) := by
    simp [lengthReturn,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,t3,hl3,valueIsWord,valueWord,
      wordOpHOL,wordOp,←BitVec.ofNat_add,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  let paid:=p1+p2+2
  refine ⟨emptyLocalsHOLFinite s3,subtotal+h2,paid,by dsimp [subtotal]; omega,by dsimp [subtotal]; omega,by dsimp [paid]; omega,?_,?_,?_⟩
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [subtotal]; omega)]
  · have firstRun : evaluateHOLFiniteState source (headerAssign "wl")=(none,s1):=run1
    have secondRun : evaluateHOLFiniteState s2 (headerAssign "total")=(none,s3):=run2
    rw [suffix_shape,WitnessRadix.StateSteps.next_sequence source s1 _ _ firstRun (by change source.clock-1-p1≤source.clock; omega)]
    rw [WitnessRadix.StateSteps.next_sequence s1 s2 _ _ assignRun (Nat.le_refl _)]
    rw [WitnessRadix.StateSteps.next_sequence s2 s3 _ _ secondRun (by change s2.clock-1-p2≤s2.clock; omega)]
    exact returnRun
  · have subtract : source.clock-1-p1-1-p2=source.clock-paid := by dsimp [paid]; omega
    change emptyLocalsHOLFinite {source with clock:=source.clock-1-p1-1-p2}=emptyLocalsHOLFinite {source with clock:=source.clock-paid}
    rw [subtract]

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.suffix_execute
