import InitECandidate.Solver.Input.RequestChain

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem chained_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor : BitVec 64) (witness : Nat)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64)))) :
    (chained source input cursor witness).locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))) ∧
    (chained source input cursor witness).locals.lookup (ofString "o_npr")=some (.val (.word 16#64)) ∧
    (chained source input cursor witness).locals.lookup (ofString "o_wit")=some (.val (.word (BitVec.ofNat 64 witness))) := by
  have base:=loaded_locals source pointer witness pointerLocal
  refine ⟨?_,?_,?_⟩
  · exact (bind_lookup_other (WitnessRadix.PersistentAlloc.post {loaded source witness with clock:=source.clock-1} cursor 96#64)
      "si" "p" cursor (by decide)).trans base.1
  · exact (bind_lookup_other (WitnessRadix.PersistentAlloc.post {loaded source witness with clock:=source.clock-1} cursor 96#64)
      "si" "o_npr" cursor (by decide)).trans base.2.1
  · exact (bind_lookup_other (WitnessRadix.PersistentAlloc.post {loaded source witness with clock:=source.clock-1} cursor 96#64)
      "si" "o_wit" cursor (by decide)).trans base.2.2

theorem pointer_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor : BitVec 64) (witness : Nat)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64)))) :
    eval (chained source input cursor witness) pointerExpression=some (.val (.word (pointer+18#64))) := by
  classical
  have locals:=chained_locals source input pointer cursor witness pointerLocal
  simp [eval,pointerExpression,localVar,evalHOLExact,evalListHOLExact,toExact,locals.1,locals.2.1,
    valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]

theorem length_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor : BitVec 64) (witness : Nat) (lower : 16≤witness)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64)))) :
    eval (positioned source input pointer cursor witness) lengthExpression=some (.val (.word (BitVec.ofNat 64 (witness-16)))) := by
  classical
  have locals:=chained_locals source input pointer cursor witness pointerLocal
  have npr : (positioned source input pointer cursor witness).locals.lookup (ofString "o_npr")=some (.val (.word 16#64)) :=
    (bind_lookup_other (chained source input cursor witness) "np" "o_npr" _ (by decide)).trans locals.2.1
  have wit : (positioned source input pointer cursor witness).locals.lookup (ofString "o_wit")=some (.val (.word (BitVec.ofNat 64 witness))) :=
    (bind_lookup_other (chained source input cursor witness) "np" "o_wit" _ (by decide)).trans locals.2.2
  have subtract : BitVec.ofNat 64 witness-16#64=BitVec.ofNat 64 (witness-16) :=
    BitVec.ofNat_sub_ofNat_of_le witness 16 (by decide) lower
  simp [eval,lengthExpression,localVar,evalHOLExact,evalListHOLExact,toExact,npr,wit,valueIsWord,valueWord,wordOpHOL,wordOp,subtract]

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.chained_locals
#print axioms InitECandidate.Solver.Input.Request.pointer_read
#print axioms InitECandidate.Solver.Input.Request.length_read
