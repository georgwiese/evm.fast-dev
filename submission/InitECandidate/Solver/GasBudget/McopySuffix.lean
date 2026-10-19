import InitECandidate.Solver.GasBudget.McopyCopyGuard
import InitECandidate.Solver.GasBudget.MemoryBufferFinish

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

set_option maxHeartbeats 1500000 in
theorem suffix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterExpansion = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ mark.toNat + (SatWord.resultWord len).toNat ≤ 33806089496 ∧ guardPrice base mark src dst len + 1 ≤ source.clock ∧
      post.clock = source.clock - (guardPrice base mark src dst len + 1) ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      post.memory (frame + 16#64) = source.memory (frame + 16#64) ∧
      (∀ query, Arenas.Outside base scratch query → CopyGeneral.Away mark query (SatWord.resultWord len).toNat →
        query ≠ frame + 0#64 → post.memory query = source.memory query) := by
  rw [afterExpansion_shape] at normal
  obtain ⟨copied, copyRun, finishRun, retained⟩ := copy_guard_safe.normal_continue source post finish returned normal
  obtain ⟨room, copyFits, copyClock, copyView, heap, away⟩ := guard_normal source copied frame base length capacity pointer scratch mark src dst len
    view srcLocal dstLocal nLocal heapGlobal domain baseLower scratchUpper markAligned markUpper headerBefore ranges copyRun
  obtain ⟨finishFits, result, finishClock, postView, budget, used, globals, finishAway⟩ :=
    MemoryFinish.normal copied post frame base length capacity pointer scratch copyView returned finishRun
  have outside (query : BitVec 64) (owned : Arenas.Outside base scratch query)
      (heapAway : CopyGeneral.Away mark query (SatWord.resultWord len).toNat) (notPC : query ≠ frame + 0#64) :
      post.memory query = source.memory query := (finishAway query notPC).trans (away query owned heapAway)
  have headerAway (offset : Nat) (inside : offset < 280) : CopyGeneral.Away mark (frame + BitVec.ofNat 64 offset) (SatWord.resultWord len).toNat := by
    have markLower : 2701131776 ≤ mark.toNat := by
      have depth := view.depth
      have cursor := view.cursor
      have order := BitVec.le_def.mp view.ordered
      have above := view.frameAbove
      omega
    have temporary : AllocatedBytes.Arena mark (SatWord.resultWord len).toNat := ⟨markLower, room⟩
    have encoded : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have headerNumber := BitVec.toNat_add_of_lt (show frame.toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 by rw [encoded]; have fits := view.frameFits; omega)
    exact temporary.away_below mark _ _ markAligned (by rw [headerNumber, encoded]; omega)
  refine ⟨result, room, ?_, ?_, postView, by rw [globals]; exact heap, ?_, ?_, ?_, outside⟩
  · rw [copyClock] at finishFits
    omega
  · rw [finishClock, copyClock]
    omega
  · unfold regularBudget wordAt
    rw [outside _ (view.header_outside 64 (by decide)) (headerAway 64 (by decide)) (offsets_ne frame _ _ (by decide)),
      outside _ (view.header_outside 184 (by decide)) (headerAway 184 (by decide)) (offsets_ne frame _ _ (by decide)),
      outside _ (view.header_outside 192 (by decide)) (headerAway 192 (by decide)) (offsets_ne frame _ _ (by decide))]
  · exact outside _ (view.header_outside 184 (by decide)) (headerAway 184 (by decide)) (offsets_ne frame _ _ (by decide))
  · exact outside _ (view.header_outside 16 (by decide)) (headerAway 16 (by decide)) (offsets_ne frame _ _ (by decide))

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.suffix_normal
