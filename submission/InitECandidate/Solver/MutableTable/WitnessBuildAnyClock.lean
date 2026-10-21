import InitECandidate.Solver.MutableTable.WitnessBuildReady
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

set_option maxRecDepth 100000

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Current physical constructor inputs give an all-outcome spent-clock
bound at any clock budget; no future successful construction is assumed. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (records table count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Ready source records table count maximum slices stp pad scratch)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) : source.clock-post.clock≤wholeVariablePrice slices count := by
  by_cases enough : wholeVariablePrice slices count≤source.clock
  · obtain ⟨bits,nextCount,input,logical,target,lower,upper,known,built,history,length,rows,control,forward,spent⟩ :=
      actual.execute source records table count maximum slices stp pad scratch enough
    have endpoint : post=target := congrArg Prod.snd (run.symm.trans known)
    rw [endpoint]
    omega
  · exact (Nat.sub_le source.clock post.clock).trans (Nat.le_of_lt (Nat.lt_of_not_ge enough))

/-- Actual normal construction at arbitrary funding yields the real built
table, arbitrary-collision history, preserved physical record cells and
original runtime control. Clock padding is only a proof transport. -/
theorem normal_any_clock (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (records table count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Ready source records table count maximum slices stp pad scratch)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word (BitVec.ofNat 64 table)) ∧ ∃ bits nextCount input logical,
      let plan:=Constructor.allocationPlan records table count (2^bits)
      2≤bits ∧ bits≤32 ∧ Layout32.Built bits post plan scratch nextCount input logical ∧ History plan input ∧ input.length=count ∧ Records post plan slices ∧
      KeccakAbsorb.hashControl post=KeccakAbsorb.hashControl {source with
        globals:=source.globals.update (Flapjack.Basis.Pure.MlString.ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} ∧
      post.clock≤source.clock ∧ source.clock-post.clock≤wholeVariablePrice slices count := by
  let padding := wholeVariablePrice slices count
  have paddedRun := panPropsEvaluateAddClockEq body source (some (.returned value)) post padding ⟨run,by intro impossible; cases impossible⟩
  have ready := actual.with_clock source records table count maximum slices stp pad scratch (source.clock+padding)
  obtain ⟨bits,nextCount,input,logical,target,lower,upper,known,built,history,length,rows,control,forward,spent⟩ :=
    ready.execute {source with clock:=source.clock+padding} records table count maximum slices stp pad scratch (Nat.le_add_left _ _)
  have resultEq := congrArg Prod.fst (known.symm.trans paddedRun)
  have answer : value=.val (.word (BitVec.ofNat 64 table)) := by cases resultEq; rfl
  have targetEq : target={post with clock:=post.clock+padding} := congrArg Prod.snd (known.symm.trans paddedRun)
  rw [targetEq] at built rows control forward spent
  have actualBuilt := Layout32.built_fields {post with clock:=post.clock+padding} post (Constructor.allocationPlan records table count (2^bits)) bits scratch nextCount input logical rfl rfl rfl built
  have actualRows : Records post (Constructor.allocationPlan records table count (2^bits)) slices := ⟨rows.pointers,rows.lengths⟩
  have actualControl : KeccakAbsorb.hashControl post=KeccakAbsorb.hashControl {source with
      globals:=source.globals.update (Flapjack.Basis.Pure.MlString.ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (table+72+57*(2^bits)+Constructor.padding (2^bits)))))} := control
  have actualForward : post.clock≤source.clock := by
    change post.clock+padding≤source.clock+padding at forward
    omega
  have actualCost : source.clock-post.clock≤wholeVariablePrice slices count := by
    change source.clock+padding-wholeVariablePrice slices count≤post.clock+padding at spent
    omega
  exact ⟨answer,bits,nextCount,input,logical,lower,upper,actualBuilt,history,length,actualRows,actualControl,actualForward,actualCost⟩

end InitECandidate.Solver.MutableTable.WitnessBuild
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.body_cost
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.normal_any_clock
