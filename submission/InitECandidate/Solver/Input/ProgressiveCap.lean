import InitECandidate.Solver.Input.CurrentHash.ProgressiveProgram
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual counter declaration computes the remaining chunk count
without modular underflow at a current in-range off value. -/
theorem count_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n off : Nat)
    (small : n<2^64) (inside : off≤n)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (position : source.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 off)))) :
    eval source countExpression=some (.val (.word (BitVec.ofNat 64 (n-off)))) := by
  have difference := BitVec.ofNat_sub_ofNat_of_le (w:=64) n off (by omega) inside
  simp [eval,countExpression,localVar,evalHOLExact,evalListHOLExact,toExact,count,position,valueIsWord,valueWord,wordOpHOL,wordOp,difference]

def capped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (size remaining : Nat) :=
  if size<remaining then bind source "cnt" (BitVec.ofNat 64 size) else source

/-- Original unsigned cap guard reaches its actual min(size,remaining)
count at the same clock, on every current state with these real bindings. -/
theorem cap_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (size remaining : Nat)
    (sizeSmall : size<2^64) (remainingSmall : remaining<2^64)
    (sizeLocal : source.locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 size))))
    (countLocal : source.locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 remaining)))) :
    evaluateHOLFiniteState source capGuard=(none,capped source size remaining) := by
  have sizeNumber : (BitVec.ofNat 64 size).toNat=size := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt sizeSmall]
  have countNumber : (BitVec.ofNat 64 remaining).toNat=remaining := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt remainingSmall]
  have read : eval source capTest=some (.val (.word (if size<remaining then 1#64 else 0#64))) := by
    simp [eval,capTest,localVar,evalHOLExact,toExact,sizeLocal,countLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,sizeNumber,countNumber]
  have readSize : eval source (localVar "size")=some (.val (.word (BitVec.ofNat 64 size))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using sizeLocal
  have assigned := StateSteps.assign_execute source "cnt" (localVar "size") (BitVec.ofNat 64 remaining) (BitVec.ofNat 64 size) countLocal readSize
  simp only [eval] at read
  rw [capGuard,evaluateHOLFiniteState_ite,read]
  by_cases smaller : size<remaining
  · simp only [if_pos smaller,capped]
    exact assigned
  · simp only [if_neg smaller,capped]
    exact evaluateHOLFiniteState_skip source

theorem capped_count (source : PanSemStateFiniteExact 64 Guest.HostMemory) (size remaining : Nat)
    (count : source.locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 remaining)))) :
    (capped source size remaining).locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 (min size remaining)))) := by
  by_cases smaller : size<remaining
  · rw [capped,if_pos smaller,Nat.min_eq_left (by omega)]
    exact bind_lookup_same _ _ _
  · rw [capped,if_neg smaller,Nat.min_eq_right (by omega)]
    exact count

theorem capped_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (size remaining : Nat) (name : String) (different : ofString "cnt"≠ofString name) :
    (capped source size remaining).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  by_cases smaller : size<remaining
  · rw [capped,if_pos smaller]
    exact bind_lookup_other _ "cnt" name _ different
  · rw [capped,if_neg smaller]

theorem capped_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (size remaining : Nat) :
    CeilLog2.frozen (capped source size remaining)=CeilLog2.frozen source ∧ (capped source size remaining).clock=source.clock := by
  unfold capped
  split <;> exact ⟨rfl,rfl⟩

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.count_read
#print axioms InitECandidate.Solver.Input.Progressive.cap_execute
#print axioms InitECandidate.Solver.Input.Progressive.capped_count
#print axioms InitECandidate.Solver.Input.Progressive.capped_other
#print axioms InitECandidate.Solver.Input.Progressive.capped_frame
