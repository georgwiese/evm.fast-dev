import InitECandidate.Solver.GasBudget.McopyCopyBranch
import InitECandidate.Solver.GasBudget.SatWordNonempty
import InitECandidate.Solver.WitnessRadix.CopyCostBounds

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

def guardPrice (base mark : BitVec 64) (src dst len : U256Value.Words) : Nat :=
  if SatWord.resultWord len = 0#64 then 0
  else copyPrice base (SatWord.resultWord src) (SatWord.resultWord dst) mark (SatWord.resultWord len).toNat + 4

theorem copy_guard_safe : Input.LocalPrefix (ofString "n") copyGuard := by
  apply Input.LocalPrefix.ite
  · apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
    apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
    apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
    apply Input.LocalPrefix.decCall _ _ _ _ (by decide)
    exact .seq (.call none _ _ (by simp)) (.seq (.call none _ _ (by simp)) (.call none _ _ (by simp)))
  · exact .skip

theorem guard_blocks (base mark : BitVec 64) (src dst len : U256Value.Words) :
    guardPrice base mark src dst len ≤ 2 * ((SatWord.resultWord len).toNat / 8) + 21 := by
  unfold guardPrice
  split
  · omega
  · have first := CopyGeneral.cost_blocks (base + SatWord.resultWord src) mark (SatWord.resultWord len).toNat
    have second := CopyGeneral.cost_blocks mark (base + SatWord.resultWord dst) (SatWord.resultWord len).toNat
    unfold copyPrice
    omega

set_option maxHeartbeats 1000000 in
theorem guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch mark : BitVec 64) (src dst len : U256Value.Words)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (srcLocal : source.locals.lookup (ofString "src") = some (U256Value.tuple src))
    (dstLocal : source.locals.lookup (ofString "dst") = some (U256Value.tuple dst))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word (SatWord.resultWord len))))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (baseLower : 2701131776 ≤ base.toNat) (scratchUpper : scratch.toNat ≤ 33806089496)
    (markAligned : mark.toNat % 8 = 0) (markUpper : mark.toNat ≤ 33806089496)
    (headerBefore : frame.toNat + 280 ≤ mark.toNat)
    (ranges : U256Zero.resultWord len = 0#64 →
      (SatWord.resultWord src).toNat + (SatWord.resultWord len).toNat ≤ length.toNat ∧
      (SatWord.resultWord dst).toNat + (SatWord.resultWord len).toNat ≤ length.toNat)
    (normal : evaluateHOLFiniteState source copyGuard = (none, post)) :
    mark.toNat + (SatWord.resultWord len).toNat ≤ 33806089496 ∧
      guardPrice base mark src dst len ≤ source.clock ∧ post.clock = source.clock - guardPrice base mark src dst len ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) ∧
      (∀ query, Arenas.Outside base scratch query → CopyGeneral.Away mark query (SatWord.resultWord len).toNat → post.memory query = source.memory query) := by
  by_cases zero : SatWord.resultWord len = 0#64
  · have skipped : evaluateHOLFiniteState source copyGuard = (none, source) := by
      simp [copyGuard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar, nLocal, zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have postEq : post = source := congrArg Prod.snd (normal.symm.trans skipped)
    rw [postEq, guardPrice, if_pos zero]
    exact ⟨by simpa [zero] using markUpper, Nat.zero_le _, by omega, view, heapGlobal, fun _ _ _ => rfl⟩
  · have branchRun : evaluateHOLFiniteState source copyBranch = (none, post) := by
      simpa [copyGuard, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, nLocal, zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using normal
    obtain ⟨sourceRange, destinationRange⟩ := ranges (SatWord.nonempty len zero)
    obtain ⟨room, funded, clock, postView, heap, away⟩ := copy_branch_normal source post frame base length capacity pointer scratch
      (SatWord.resultWord len) mark src dst view srcLocal dstLocal nLocal heapGlobal domain baseLower scratchUpper markAligned markUpper
      headerBefore sourceRange destinationRange branchRun
    rw [guardPrice, if_neg zero]
    exact ⟨room, funded, clock, postView, heap, away⟩

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.copy_guard_safe
#print axioms InitECandidate.Solver.GasBudget.Mcopy.guard_blocks
#print axioms InitECandidate.Solver.GasBudget.Mcopy.guard_normal
