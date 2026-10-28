import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteReads
import InitECandidate.Solver.Input.MemeqCode
import InitECandidate.Solver.Input.MemeqReadOnly
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Environment
import InitECandidate.Solver.WitnessRadix.MemeqMemory
import InitECandidate.Solver.Input.ScopedCallClassified
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.Input.CurrentTable.Compare
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

noncomputable local instance : DecidableEq KeyBits.Key := Classical.decEq _

/-- The existing byte-equality executor uses exactly these physical bytes;
it does not inspect either dictionary's bit-order convention. -/
theorem memory_view (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (key : KeyBits.Key) (view : FirstDiff.ByteView source pointer key) :
    MemoryBytes.ByteView source pointer key := view

/-- All current32-byte comparison outcomes cost at most four body clocks,
from actual physical bytes at arbitrary alignment. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (left right : KeyBits.Key)
    (aCell : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bCell : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (lengthCell : source.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (aView : FirstDiff.ByteView source a left) (bView : FirstDiff.ByteView source b right)
    (aFits : a.toNat+32 < 2^64) (bFits : b.toNat+32 < 2^64) (little : source.be = false) :
    source.clock-(evaluateHOLFiniteState source Memeq32.body).2.clock ≤ 4 := by
  by_cases enough : 4 ≤ source.clock
  · obtain ⟨paid,bounded,run⟩ := Memeq32.memory_execute source a b left right aCell bCell lengthCell
      (memory_view source a left aView) (memory_view source b right bView) aFits bFits little enough
    rw [run]
    change source.clock-(source.clock-paid) ≤ 4
    omega
  · omega

/-- A genuine current comparison return identifies equality of the actual
keys and retains the full physical frame. Padding is used only to invert
that real normal execution, not as assumed runtime funding. -/
theorem body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (left right : KeyBits.Key)
    (aCell : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bCell : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (lengthCell : source.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (aView : FirstDiff.ByteView source a left) (bView : FirstDiff.ByteView source b right)
    (aFits : a.toNat+32 < 2^64) (bFits : b.toNat+32 < 2^64) (little : source.be = false)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Memeq32.body = (some (.returned value),post)) :
    value = .val (.word (if left = right then 1#64 else 0#64)) ∧ LocalEffects.erase post = LocalEffects.erase source := by
  let padded := {source with clock := source.clock+4}
  have paddedLeft : FirstDiff.ByteView padded a left := aView.of_frame rfl
  have paddedRight : FirstDiff.ByteView padded b right := bView.of_frame rfl
  obtain ⟨paid,bounded,run⟩ := Memeq32.memory_execute padded a b left right aCell bCell lengthCell
    (memory_view padded a left paddedLeft) (memory_view padded b right paddedRight) aFits bFits little (by change 4 ≤ source.clock+4; omega)
  have lifted := panPropsEvaluateAddClockEq Memeq32.body source (some (.returned value)) post 4
    ⟨normal,by intro impossible; cases impossible⟩
  have observed := congrArg Prod.fst (lifted.symm.trans run)
  have answer : value = .val (.word (if left = right then 1#64 else 0#64)) := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using observed
  have frame := MutableTable.MemeqAny.readonly source.code source rfl
  rw [normal] at frame
  exact ⟨answer,frame⟩

/-- The current Software ABI is checked by MemeqAny.original_code. The
actual caller stops within five ticks or continues with the genuine byte
comparison result and unchanged physical table/input state. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (left right : KeyBits.Key)
    (aView : FirstDiff.ByteView source a left) (bView : FirstDiff.ByteView source b right)
    (aFits : a.toNat+32 < 2^64) (bFits : b.toNat+32 < 2^64) (little : source.be = false)
    (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word a),.val (.word b),.val (.word 32#64)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "memeq") expressions continuation) = (outcome,post)) :
    (source.clock-post.clock ≤ 5 ∧ ∀ value,outcome ≠ some (.returned value)) ∨
      ∃ target inner,LocalEffects.erase target = LocalEffects.erase source ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 5 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name
          (.val (.word (if left = right then 1#64 else 0#64)))) continuation = (outcome,inner) ∧ post = restore source name inner := by
  obtain ⟨callee,called,aCell,bCell,lengthCell⟩ := MutableTable.MemeqByteRuntime.environment source.code.lookup a b 32
    (MutableTable.MemeqAny.original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have readyLeft : FirstDiff.ByteView entry a left := aView.of_frame rfl
  have readyRight : FirstDiff.ByteView entry b right := bView.of_frame rfl
  have price := body_cost entry a b left right aCell bCell lengthCell readyLeft readyRight aFits bFits little
  rcases CallNormal.scoped_classified source post name .one (ofString "memeq") expressions _ Memeq32.body continuation callee .one 4
    args called price outcome run with stopped | reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨answer,frame⟩ := body_returned entry target a b left right aCell bCell lengthCell readyLeft readyRight aFits bFits little value bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,inner,frame,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentTable.Compare

#print axioms InitECandidate.Solver.Input.CurrentTable.Compare.body_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Compare.body_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.Compare.scoped_trace
