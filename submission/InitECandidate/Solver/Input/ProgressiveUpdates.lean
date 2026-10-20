import InitECandidate.Solver.Input.ProgressiveCap

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def advanced (source : PanSemStateFiniteExact 64 Guest.HostMemory) (off size k : BitVec 64) :=
  bind (bind (bind source "off" (off+size)) "size" (size<<<(2:Nat))) "k" (k+1#64)

/-- The three actual original updates, including the left-shift by two,
execute at zero source-clock cost from their real current caller bindings. -/
theorem updates_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (off size k : BitVec 64)
    (position : source.locals.lookup (ofString "off")=some (.val (.word off)))
    (sizeLocal : source.locals.lookup (ofString "size")=some (.val (.word size)))
    (round : source.locals.lookup (ofString "k")=some (.val (.word k))) :
    evaluateHOLFiniteState source updates=(none,advanced source off size k) := by
  let first := bind source "off" (off+size)
  let second := bind first "size" (size<<<(2:Nat))
  have offRead : eval source (.op .add [localVar "off",localVar "size"])=some (.val (.word (off+size))) := by
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,position,sizeLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
  have firstRun := StateSteps.assign_execute source "off" _ off (off+size) position offRead
  have firstSize : first.locals.lookup (ofString "size")=some (.val (.word size)) := (bind_lookup_other source "off" "size" (off+size) (by decide)).trans sizeLocal
  have sizeRead : eval first (.shift .lsl (localVar "size") (.const 2#64))=some (.val (.word (size<<<(2:Nat)))) := by
    simp [eval,localVar,evalHOLExact,toExact,firstSize,wordShiftHOL]
  have secondRun := StateSteps.assign_execute first "size" _ size (size<<<(2:Nat)) firstSize sizeRead
  have secondK : second.locals.lookup (ofString "k")=some (.val (.word k)) :=
    (bind_lookup_other first "size" "k" (size<<<(2:Nat)) (by decide)).trans ((bind_lookup_other source "off" "k" (off+size) (by decide)).trans round)
  have kRead : eval second (.op .add [localVar "k",.const 1#64])=some (.val (.word (k+1#64))) := by
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,secondK,valueIsWord,valueWord,wordOpHOL,wordOp]
  have thirdRun := StateSteps.assign_execute second "k" _ k (k+1#64) secondK kRead
  rw [updates,StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _)]
  exact thirdRun

theorem advanced_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (off size k : BitVec 64) :
    (advanced source off size k).locals.lookup (ofString "off")=some (.val (.word (off+size))) ∧
    (advanced source off size k).locals.lookup (ofString "size")=some (.val (.word (size<<<(2:Nat)))) ∧
    (advanced source off size k).locals.lookup (ofString "k")=some (.val (.word (k+1#64))) ∧
    CeilLog2.frozen (advanced source off size k)=CeilLog2.frozen source ∧ (advanced source off size k).clock=source.clock := by
  refine ⟨?_,?_,bind_lookup_same _ _ _,rfl,rfl⟩
  · exact (bind_lookup_other _ "k" "off" _ (by decide)).trans ((bind_lookup_other _ "size" "off" _ (by decide)).trans (bind_lookup_same _ _ _))
  · exact (bind_lookup_other _ "k" "size" _ (by decide)).trans (bind_lookup_same _ _ _)

/-- Bit-vector updates agree with the original geometric natural values;
this is modular equality, so no future range assumption is hidden here. -/
theorem advanced_geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) :
    (advanced source (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k)).locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 (offset (k+1))))) ∧
    (advanced source (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k)).locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 (4^(k+1))))) ∧
    (advanced source (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k)).locals.lookup (ofString "k")=some (.val (.word (BitVec.ofNat 64 (k+1)))) := by
  have shifted : ((BitVec.ofNat 64 (4^k))<<<(2:Nat))=BitVec.ofNat 64 (4^(k+1)) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.pow_succ,Nat.mul_mod]
  have fields := advanced_fields source (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k)
  refine ⟨?_,?_,?_⟩
  · simpa only [offset,BitVec.ofNat_add] using fields.1
  · simpa only [shifted] using fields.2.1
  · simpa only [BitVec.ofNat_add] using fields.2.2.1

def pairEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n off size : Nat) :=
  capped (bind source "cnt" (BitVec.ofNat 64 (n-off))) size (n-off)

/-- Exact original progressive declaration/cap prefix, valid for all later
outcomes at the current count/offset/size. All caller scope is restored. -/
theorem step_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n off size : Nat)
    (small : n<2^64) (inside : off≤n) (sizeSmall : size<2^64)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (position : source.locals.lookup (ofString "off")=some (.val (.word (BitVec.ofNat 64 off))))
    (sizeLocal : source.locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 size)))) :
    evaluateHOLFiniteState source step=(let output:=evaluateHOLFiniteState (pairEntry source n off size) afterCap;
      (output.1,restore source "cnt" output.2)) := by
  let entry := bind source "cnt" (BitVec.ofNat 64 (n-off))
  have entrySize : entry.locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 size))) :=
    (bind_lookup_other source "cnt" "size" (BitVec.ofNat 64 (n-off)) (by decide)).trans sizeLocal
  have capRun := cap_execute entry size (n-off) sizeSmall (by omega) entrySize (bind_lookup_same _ _ _)
  have capSequence := StateSteps.next_sequence entry (pairEntry source n off size) capGuard afterCap capRun (capped_frame entry size (n-off)).2.le
  let output := evaluateHOLFiniteState (pairEntry source n off size) afterCap
  have declared := ScalarScope.declare_execute source output.2 "cnt" countExpression (BitVec.ofNat 64 (n-off)) afterCount output.1
    (count_read source n off small inside count position) (by rw [afterCount,capSequence])
  rw [loop_shape.2]
  exact declared

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.updates_execute
#print axioms InitECandidate.Solver.Input.Progressive.advanced_fields
#print axioms InitECandidate.Solver.Input.Progressive.advanced_geometry
#print axioms InitECandidate.Solver.Input.Progressive.step_prefix
