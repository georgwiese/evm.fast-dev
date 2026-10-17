import InitECandidate.Solver.WitnessRadix.ZeroBlock
import InitECandidate.Solver.WitnessRadix.Copy32Alignment

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

theorem condition_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index length step : Nat)
    (small : length + 32 < 2 ^ 64) (ordered : index ≤ length) (stepBound : step ≤ 32)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address))
      (condition (BitVec.ofNat 64 step)) = some (.val (.word (if index + step ≤ length then 1#64 else 0#64))) := by
  classical
  have indexSmall : index < 2 ^ 64 := by omega
  have lengthSmall : length < 2 ^ 64 := by omega
  have stepSmall : step < 2 ^ 64 := by omega
  have sum : (BitVec.ofNat 64 index + BitVec.ofNat 64 step).toNat = index + step := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases active : index + step ≤ length
  · have less : ¬ (BitVec.ofNat 64 length < BitVec.ofNat 64 index + BitVec.ofNat 64 step) := by
      change ¬ (BitVec.ofNat 64 length).toNat < _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthSmall, sum]
      omega
    simp [condition, Copy32.condition, localVar, addConst, evalHOLFinite, evalHOLExact, evalListHOLExact,
      toExact, indexLocal, lengthLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, less, active]
  · have less : BitVec.ofNat 64 length < BitVec.ofNat 64 index + BitVec.ofNat 64 step := by
      change (BitVec.ofNat 64 length).toNat < _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthSmall, sum]
      omega
    simp [condition, Copy32.condition, localVar, addConst, evalHOLFinite, evalHOLExact, evalListHOLExact,
      toExact, indexLocal, lengthLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, less, active]

theorem alignment_read {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst))) (aligned : dst.toNat % 8 = 0) :
    eval source alignment = some (.val (.word 1#64)) := by
  have mask := Copy32.aligned_mask dst aligned
  simp [eval, alignment, localVar, evalHOLExact, evalListHOLExact, toExact, dstLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, mask]

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.condition_read
#print axioms InitECandidate.Solver.WitnessRadix.Zero.alignment_read
