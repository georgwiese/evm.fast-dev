import InitECandidate.Solver.WitnessRadix.KeccakAbsorbLane

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

structure Mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (stp blk : BitVec 64) (unaligned : Bool) : Prop where
  stateWords : ∀ lane : Fin 25, source.memaddrs (byteAddress stp (8*lane.val))
  blockWords : unaligned = false → ∀ lane : Fin 17, source.memaddrs (byteAddress blk (8*lane.val))
  blockBytes : ∀ offset : Fin 136, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress blk offset.val))

theorem condition_read {F : Type} (source : PanSemStateFiniteExact 64 F) (lane : Nat) (inside : lane ≤ 17)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (8*lane))))) :
    @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address)) condition =
      some (.val (.word (if lane < 17 then 1#64 else 0#64))) := by
  have small : 8*lane < 2^64 := by omega
  have sign : 8*lane < 2^63 := by omega
  by_cases active : lane < 17
  · have h : 8*lane < 136 := by omega
    simp [condition, localVar, evalHOLFinite, evalHOLExact, toExact, indexLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, sign, h, active]
  · have h : ¬ 8*lane < 136 := by omega
    simp [condition, localVar, evalHOLFinite, evalHOLExact, toExact, indexLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, sign, h, active]

noncomputable def stateLanes {F : Type} (source : PanSemStateFiniteExact 64 F) (stp : BitVec 64) (unaligned : Bool) (lane : Nat) :
    Nat → PanSemStateFiniteExact 64 F
  | 0 => source
  | rounds + 1 => stateLanes (lanePost (decClockHOLFinite source) stp (BitVec.ofNat 64 (8*lane)) unaligned) stp unaligned (lane+1) rounds

/-- The complete actual 17-lane absorption loop, aligned or byte-expanded,
from mapped memory and ABI facts. Exactly one source clock per lane. -/
theorem loop_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (stp blk : BitVec 64) (unaligned : Bool) (lane rounds : Nat)
    (count : lane + rounds = 17)
    (stpLocal : source.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (blkLocal : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (8*lane)))))
    (mapped : Mapped source stp blk unaligned) (enough : rounds ≤ source.clock) :
    evaluateHOLFiniteState source (loop unaligned) = (none, stateLanes source stp unaligned lane rounds) := by
  classical
  induction rounds generalizing source lane with
  | zero =>
    have testRun := condition_read source lane (by omega) indexLocal
    have inactive : ¬ lane < 17 := by omega
    simp only [if_neg inactive] at testRun
    rw [loop, evaluateHOLFiniteState_while_total, testRun]
    simp [stateLanes]
  | succ rounds ih =>
    have active : lane < 17 := by omega
    have nonzero : source.clock ≠ 0 := by omega
    let entry := decClockHOLFinite source
    let next := lanePost entry stp (BitVec.ofNat 64 (8*lane)) unaligned
    have stateMapped : entry.memaddrs (stp + BitVec.ofNat 64 (8*lane)) := mapped.stateWords ⟨lane, by omega⟩
    have wordMapped : unaligned = false → entry.memaddrs (blk + BitVec.ofNat 64 (8*lane)) := by
      intro h; exact mapped.blockWords h ⟨lane, active⟩
    have byteMapped : ∀ offset : Fin 8, entry.memaddrs (panByteAlignHOL (width := 64)
        (blk + BitVec.ofNat 64 (8*lane) + BitVec.ofNat 64 offset.val)) := by
      intro offset
      have h := mapped.blockBytes ⟨8*lane+offset.val, by have := offset.isLt; omega⟩
      simpa only [entry, decClockHOLFinite, byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using h
    have bodyRun := lane_execute entry stp blk (BitVec.ofNat 64 (8*lane)) unaligned stpLocal blkLocal indexLocal stateMapped wordMapped byteMapped
    have nextStp : next.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
      rw [lane_other entry _ _ _ _ (by decide)]; exact stpLocal
    have nextBlk : next.locals.lookup (ofString "blk") = some (.val (.word blk)) := by
      rw [lane_other entry _ _ _ _ (by decide)]; exact blkLocal
    have nextIndex : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (8*(lane+1))))) := by
      change (bind _ "i" _).locals.lookup (ofString "i") = _
      rw [bind_lookup_same, BitVec.ofNat_add_ofNat (8*lane) 8]
      have h : 8*lane+8 = 8*(lane+1) := by omega
      rw [h]
    have nextMapped : Mapped next stp blk unaligned := ⟨mapped.stateWords, mapped.blockWords, mapped.blockBytes⟩
    have tailRun := ih next (lane+1) (by omega) nextStp nextBlk nextIndex nextMapped (by change rounds ≤ source.clock-1; omega)
    have testRun := condition_read source lane (by omega) indexLocal
    simp only [if_pos active] at testRun
    rw [loop, evaluateHOLFiniteState_while_total, testRun]
    simp only [show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide, ↓reduceIte, if_neg nonzero]
    rw [bodyRun, StateSteps.fixed_clock entry next none (Nat.le_refl _)]
    exact tailRun

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.condition_read
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.loop_execute
