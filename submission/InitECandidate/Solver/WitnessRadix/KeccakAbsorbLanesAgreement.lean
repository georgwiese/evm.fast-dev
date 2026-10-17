import InitECandidate.Solver.WitnessRadix.KeccakAbsorbAgreement

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Only the actual state and input read cells must lie in the agreed region.
Unrelated private allocations can occur anywhere else. -/
structure ReadRegion (region : BitVec 64 → Prop) (stp blk : BitVec 64) (unaligned : Bool) : Prop where
  stateWords : ∀ lane : Fin 17, region (byteAddress stp (8 * lane.val))
  blockWords : unaligned = false → ∀ lane : Fin 17, region (byteAddress blk (8 * lane.val))
  blockBytes : ∀ offset : Fin 136,
    region (panByteAlignHOL (width := 64) (byteAddress blk offset.val))

theorem stateLanes_memory_agrees {F : Type}
    (source target : PanSemStateFiniteExact 64 F) (stp blk : BitVec 64) (unaligned : Bool)
    (lane rounds : Nat) (count : lane + rounds ≤ 17)
    (sourceBlk : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (targetBlk : target.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (sourceIndex : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (8 * lane)))))
    (targetIndex : target.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (8 * lane)))))
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (region : BitVec 64 → Prop) (reads : ReadRegion region stp blk unaligned)
    (same : ∀ query, region query → source.memory query = target.memory query) :
    ∀ query, region query →
      (stateLanes source stp unaligned lane rounds).memory query =
      (stateLanes target stp unaligned lane rounds).memory query := by
  induction rounds generalizing source target lane with
  | zero => exact same
  | succ rounds ih =>
    let leftEntry := decClockHOLFinite source
    let rightEntry := decClockHOLFinite target
    let leftNext := lanePost leftEntry stp (BitVec.ofNat 64 (8 * lane)) unaligned
    let rightNext := lanePost rightEntry stp (BitVec.ofNat 64 (8 * lane)) unaligned
    have active : lane < 17 := by omega
    have input := input_value_agrees leftEntry rightEntry blk (BitVec.ofNat 64 (8 * lane)) unaligned
      sourceBlk targetBlk sourceIndex targetIndex domain endian
      (by intro aligned; exact same _ (reads.blockWords aligned ⟨lane, active⟩))
      (by
        intro offset
        have cell := reads.blockBytes ⟨8 * lane + offset.val, by have := offset.isLt; omega⟩
        exact same _ (by simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using cell))
    have nextSame := lane_memory_agrees leftEntry rightEntry stp (BitVec.ofNat 64 (8 * lane))
      unaligned region same (reads.stateWords ⟨lane, active⟩) input
    have leftBlk : leftNext.locals.lookup (ofString "blk") = some (.val (.word blk)) := by
      rw [lane_other _ _ _ _ _ (by decide)]
      exact sourceBlk
    have rightBlk : rightNext.locals.lookup (ofString "blk") = some (.val (.word blk)) := by
      rw [lane_other _ _ _ _ _ (by decide)]
      exact targetBlk
    have indexStep : BitVec.ofNat 64 (8 * lane) + 8#64 = BitVec.ofNat 64 (8 * (lane + 1)) := by
      rw [BitVec.ofNat_add_ofNat (8 * lane) 8]
      congr 1
    have leftIndex : leftNext.locals.lookup (ofString "i") =
        some (.val (.word (BitVec.ofNat 64 (8 * (lane + 1))))) := by
      change (bind _ "i" _).locals.lookup (ofString "i") = _
      rw [bind_lookup_same, indexStep]
    have rightIndex : rightNext.locals.lookup (ofString "i") =
        some (.val (.word (BitVec.ofNat 64 (8 * (lane + 1))))) := by
      change (bind _ "i" _).locals.lookup (ofString "i") = _
      rw [bind_lookup_same, indexStep]
    exact ih leftNext rightNext (lane + 1) (by omega) leftBlk rightBlk leftIndex rightIndex
      domain endian nextSame

theorem prepared_memory_agrees
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64)
    (sourceBlk : source.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (targetBlk : target.locals.lookup (ofString "blk") = some (.val (.word blk)))
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (region : BitVec 64 → Prop) (reads : ReadRegion region stp blk (isUnaligned blk))
    (same : ∀ query, region query → source.memory query = target.memory query) :
    ∀ query, region query →
      (prepared source stp blk).memory query = (prepared target stp blk).memory query := by
  apply stateLanes_memory_agrees (bind source "i" 0#64) (bind target "i" 0#64)
    stp blk (isUnaligned blk) 0 17 (by omega)
  · exact (bind_lookup_other source "i" "blk" _ (by decide)).trans sourceBlk
  · exact (bind_lookup_other target "i" "blk" _ (by decide)).trans targetBlk
  · exact bind_lookup_same _ _ _
  · exact bind_lookup_same _ _ _
  · exact domain
  · exact endian
  · exact reads
  · exact same

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.stateLanes_memory_agrees
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.prepared_memory_agrees
