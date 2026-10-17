import InitECandidate.Solver.Input.VarList.Layout

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def badRecord (current first total previous : BitVec 64) : Prop :=
  current.toNat<first.toNat ∨ total.toNat<current.toNat ∨ current.toNat<previous.toNat
instance badRecordDecidable (current first total previous : BitVec 64) : Decidable (badRecord current first total previous) := by
  unfold badRecord
  infer_instance

theorem record_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (current first total previous : BitVec 64)
    (o : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (p : source.locals.lookup (ofString "prev")=some (.val (.word previous))) :
    eval source recordTest=some (.val (.word (if badRecord current first total previous then 1#64 else 0#64))) := by
  classical
  by_cases low : current.toNat<first.toNat <;> by_cases high : total.toNat<current.toNat <;> by_cases prior : current.toNat<previous.toNat <;>
    simp [eval,recordTest,badRecord,localVar,evalHOLExact,evalListHOLExact,toExact,o,f,n,p,valueIsWord,valueWord,
      wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,low,high,prior,OrOp.or]

theorem has_previous_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (small : index<2^63)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source hasPrevious=some (.val (.word (if 0<index then 1#64 else 0#64))) := by
  classical
  have sign : index<9223372036854775808 := small
  have encoded : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [eval,hasPrevious,localVar,evalHOLExact,toExact,i,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,BitVec.lt_def,encoded,sign]

theorem loop_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index count : Nat)
    (indexSmall : index<2^63) (countSmall : count<2^63)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 count)))) :
    eval source loopTest=some (.val (.word (if index<count then 1#64 else 0#64))) := by
  classical
  have indexSign : index<9223372036854775808 := indexSmall
  have countSign : count<9223372036854775808 := countSmall
  have ie : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ne : (BitVec.ofNat 64 count).toNat=count := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [eval,loopTest,localVar,evalHOLExact,toExact,i,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,BitVec.lt_def,ie,ne,indexSign,countSign]

/-- The actual per-record guard changes nothing on valid offsets; rejection
raises SszErr23 in one call clock and cannot proceed to any record write. -/
theorem record_guard (source : PanSemStateFiniteExact 64 Guest.HostMemory) (current first total previous : BitVec 64)
    (o : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (p : source.locals.lookup (ofString "prev")=some (.val (.word previous)))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source recordGuard=
      if badRecord current first total previous then
        (some (.exception (ofString "SszErr") (.val (.word 23#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else (none,source) :=
  Header.test_guard_execute source recordTest 23#64 _ (record_test_read source current first total previous o f n p) failCode exceptionShape enough

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.record_test_read
#print axioms InitECandidate.Solver.Input.VarList.has_previous_read
#print axioms InitECandidate.Solver.Input.VarList.loop_test_read
#print axioms InitECandidate.Solver.Input.VarList.record_guard
