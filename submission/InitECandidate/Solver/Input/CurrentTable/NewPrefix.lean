import InitECandidate.Solver.Input.CurrentTable.NewProgram
import InitECandidate.Solver.Input.CurrentAllocationTrace
import InitECandidate.Solver.WitnessRadix.AllocatedArena

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def tableEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 88#64) "t" heap
def strideEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) := bind (tableEntry source heap) "stride" 32#64
def fieldsEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64) := bind (strideEntry source heap) "ncap" cap

def restorePrefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "t" (restore (tableEntry source heap) "stride" (restore (strideEntry source heap) "ncap" target))

/-- At the genuine32-byte-key table caller, the current stride expression
and minimum-capacity guard have their literal normal behavior. -/
theorem prefix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cap : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat) :
    evaluateHOLFiniteState source afterTable=
      let ready:=bind (bind source "stride" 32#64) "ncap" cap
      let output:=evaluateHOLFiniteState ready fields
      (output.1,restore source "stride" (restore (bind source "stride" 32#64) "ncap" output.2)) := by
  have strideRead : eval source strideExpression=some (.val (.word 32#64)) := by
    simp [strideExpression,eval,evalHOLExact,evalListHOLExact,toExact,localVar,keyLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
    decide
  let first:=bind source "stride" 32#64
  have capRead : eval first (localVar "cap")=some (.val (.word cap)) := by
    have kept:=(bind_lookup_other source "stride" "cap" 32#64 (by decide)).trans capLocal
    simp [eval,evalHOLExact,toExact,localVar,first,kept]
  let ready:=bind first "ncap" cap
  have ncapLocal : ready.locals.lookup (ofString "ncap")=some (.val (.word cap)) := bind_lookup_same _ _ _
  have guard : evaluateHOLFiniteState ready capacityGuard=(none,ready) := by
    simp [capacityGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,ncapLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,show ¬cap.toNat<2 from by omega]
  have afterRun : evaluateHOLFiniteState ready afterNcap=evaluateHOLFiniteState ready fields := by
    rw [shapes.2.2.2,evaluateHOLFiniteState_seq_line780,guard]
  let output:=evaluateHOLFiniteState ready fields
  have innerRun : evaluateHOLFiniteState ready afterNcap=(output.1,output.2) := afterRun
  have firstRun : evaluateHOLFiniteState first afterStride=(output.1,restore first "ncap" output.2) := by
    rw [shapes.2.2.1]
    exact ScalarScope.declare_execute first output.2 "ncap" (localVar "cap") cap afterNcap output.1 capRead innerRun
  rw [shapes.2.1]
  exact ScalarScope.declare_execute source (restore first "ncap" output.2) "stride" strideExpression 32#64 afterStride output.1 strideRead firstRun

/-- Every actual Patricia-constructor outcome either stops within the
first allocation allowance or derives its fresh88-byte header and reaches
its real first field store. No room is assumed for this or later arrays. -/
theorem entry_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤2 ∧ ∀ value,outcome≠some (.returned value)) ∨
      1≤source.clock ∧ heap.toNat+88≤2952790016 ∧ AllocatedBytes.Arena heap 88 ∧
      ∃ inner,evaluateHOLFiniteState (fieldsEntry source heap cap) fields=(outcome,inner) ∧ post=restorePrefix source heap inner := by
  rw [shapes.1] at run
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 88#64]=some (PersistentAlloc.values 88#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  rcases CurrentAlloc.scoped_classified source post "t" [.const 88#64] afterTable heap 88#64 args installed heapCell heapBound outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨funded,room,middle,continued,endpoint⟩:=reached
    change evaluateHOLFiniteState (tableEntry source heap) afterTable=(outcome,middle) at continued
    have keyKept : (tableEntry source heap).locals.lookup (ofString "key_len")=some (.val (.word 32#64)) :=
      (bind_lookup_other _ "t" "key_len" heap (by decide)).trans keyLocal
    have capKept : (tableEntry source heap).locals.lookup (ofString "cap")=some (.val (.word cap)) :=
      (bind_lookup_other _ "t" "cap" heap (by decide)).trans capLocal
    rw [prefix_execute (tableEntry source heap) cap keyKept capKept atLeastTwo] at continued
    let inner:=(evaluateHOLFiniteState (fieldsEntry source heap cap) fields).2
    have observed:=congrArg Prod.fst continued
    have restored:=congrArg Prod.snd continued
    dsimp only at observed restored
    change heap.toNat+88≤2952790016 at room
    exact Or.inr ⟨funded,room,⟨by omega,by omega⟩,inner,Prod.ext observed rfl,by rw [endpoint,←restored]; rfl⟩

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.prefix_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.New.entry_trace
