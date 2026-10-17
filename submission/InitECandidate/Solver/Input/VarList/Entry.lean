import InitECandidate.Solver.Input.VarList.Program

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

def emptyValue : ValueHOL 64 := .rStruct [.val (.word 0#64),.val (.word 0#64)]

theorem empty_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (small : length<2^64)
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source emptyTest=some (.val (.word (if length=0 then 1#64 else 0#64))) := by
  classical
  have encoded : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have zero : BitVec.ofNat 64 length=0#64↔length=0 := by
    constructor
    · intro eq
      have h:=congrArg BitVec.toNat eq
      rw [encoded] at h
      exact h
    · intro eq
      rw [eq]
  simp [eval,emptyTest,localVar,evalHOLExact,toExact,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]

theorem empty_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (small : length<2^64)
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    evaluateHOLFiniteState source emptyGuard=
      if length=0 then (some (.returned emptyValue),emptyLocalsHOLFinite source) else (none,source) := by
  classical
  have test:=empty_test_read source length small n
  simp only [eval] at test
  have returned : evaluateHOLFiniteState source emptyReturn=(some (.returned emptyValue),emptyLocalsHOLFinite source) := by
    simp [emptyReturn,emptyValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rw [emptyGuard,evaluateHOLFiniteState_ite,test]
  by_cases empty : length=0
  · simp only [if_pos empty]
    simpa using returned
  · simp only [if_neg empty]
    simp

/-- Empty and short slices follow the real early return/error paths. Otherwise
all four first-offset bytes are read from the copied input, entering the actual
remaining function body with the lexical restoration retained. -/
theorem entry_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (start length : Nat) (heap : Blob.HeapInput source input pointer)
    (inside : start+length≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source body=
      if length=0 then (some (.returned emptyValue),emptyLocalsHOLFinite source)
      else if length<4 then (some (.exception (ofString "SszErr") (.val (.word 20#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else (let output:=evaluateHOLFiniteState (bind source "first" (BitVec.ofNat 64 (Guest.GasLimit.le32 input start))) firstTail;
        (output.1,restore source "first" output.2)) := by
  classical
  have extent : input.length%2^64<2^64 := Nat.mod_lt _ (by decide)
  have small : length<2^64 := by omega
  have emptyRun:=empty_execute source length small n
  have shortRun : evaluateHOLFiniteState source shortGuard=
      if length<4 then (some (.exception (ofString "SszErr") (.val (.word 20#64))),emptyLocalsHOLFinite {source with clock:=source.clock-1})
      else (none,source) :=
    Header.length_guard_execute source length 4 20 small (by decide) n failCode exceptionShape enough
  rw [entry_shape]
  by_cases empty : length=0
  · simp only [if_pos empty] at emptyRun ⊢
    exact WitnessRadix.StateSteps.stopped_sequence source _ emptyGuard (.seq shortGuard (.dec (ofString "first") .one firstExpression firstTail)) _ emptyRun (Nat.le_refl _)
  · simp only [if_neg empty] at emptyRun ⊢
    rw [WitnessRadix.StateSteps.next_sequence source source emptyGuard _ emptyRun (Nat.le_refl _)]
    by_cases short : length<4
    · simp only [if_pos short] at shortRun ⊢
      exact WitnessRadix.StateSteps.stopped_sequence source _ shortGuard (.dec (ofString "first") .one firstExpression firstTail) _ shortRun (by change source.clock-1≤source.clock; omega)
    · simp only [if_neg short] at shortRun ⊢
      rw [WitnessRadix.StateSteps.next_sequence source source shortGuard _ shortRun (Nat.le_refl _)]
      have pRead : eval source (localVar "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))) := by
        simpa [eval,localVar,evalHOLExact,toExact] using p
      have firstRead:=Scalar.flat_heap_le32 source input pointer (pointer+BitVec.ofNat 64 start) (localVar "p") [] start heap (by omega) pRead (by simp)
      have setup : Executes source [.declare "first" firstExpression]
          (bind source "first" (BitVec.ofNat 64 (Guest.GasLimit.le32 input start))) (fun target=>restore source "first" target) :=
        Executes.declare (restoreRest:=id) _ firstRead (Executes.done _)
      exact WitnessRadix.ProgramPrefix.execute setup firstTail

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.empty_test_read
#print axioms InitECandidate.Solver.Input.VarList.empty_execute
#print axioms InitECandidate.Solver.Input.VarList.entry_execute
