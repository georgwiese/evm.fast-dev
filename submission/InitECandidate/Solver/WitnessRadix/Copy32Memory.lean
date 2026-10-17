import InitECandidate.Solver.WitnessRadix.Copy32Execution

namespace InitECandidate.Solver.WitnessRadix.Copy32
open Flapjack PanSemStateFiniteExact

theorem writes_distinct (dst : BitVec 64) (fits : dst.toNat + 32 < 2 ^ 64) (words : Fin 4 → BitVec 64) :
    ((writes dst words).map Prod.fst).Nodup := by
  have apart (left right : Nat) (l : left < 32) (r : right < 32) (different : left ≠ right) :=
    byteAddress_ne dst left right (by omega) (by omega) different
  have a01 : dst ≠ dst + 8#64 := by simpa [byteAddress] using apart 0 8 (by decide) (by decide) (by decide)
  have a02 : dst ≠ dst + 16#64 := by simpa [byteAddress] using apart 0 16 (by decide) (by decide) (by decide)
  have a03 : dst ≠ dst + 24#64 := by simpa [byteAddress] using apart 0 24 (by decide) (by decide) (by decide)
  have a12 : dst + 8#64 ≠ dst + 16#64 := apart 8 16 (by decide) (by decide) (by decide)
  have a13 : dst + 8#64 ≠ dst + 24#64 := apart 8 24 (by decide) (by decide) (by decide)
  have a23 : dst + 16#64 ≠ dst + 24#64 := apart 16 24 (by decide) (by decide) (by decide)
  simp [writes, List.nodup_cons, a01, a02, a03, a12, a13, a23]

theorem write_member (dst : BitVec 64) (words : Fin 4 → BitVec 64) (limb : Fin 4) :
    (dst + BitVec.ofNat 64 (8 * limb.val), words limb) ∈ writes dst words := by
  obtain ⟨limb, bound⟩ := limb
  cases limb with
  | zero => simp [writes]
  | succ limb => cases limb with
    | zero => simp [writes]
    | succ limb => cases limb with
      | zero => simp [writes]
      | succ limb => cases limb with
        | zero => simp [writes]
        | succ limb => omega

/-- The copied destination has exactly the original four word values. -/
theorem word_view {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (words : Fin 4 → BitVec 64)
    (fits : dst.toNat + 32 < 2 ^ 64)
    (mapped : ∀ limb : Fin 4, source.memaddrs (dst + BitVec.ofNat 64 (8 * limb.val))) :
    MemoryBytes.WordView { source with memory := memory source.memory dst words } dst words := by
  refine ⟨mapped, ?_⟩
  intro limb
  exact WordWrites.write_unique source.memory (writes dst words) _ (writes_distinct dst fits words) (write_member dst words limb)

/-- The concrete word stores preserve the original 32 hash bytes at the new
aligned destination, without an assumed copying oracle. -/
theorem byte_view {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (words : Fin 4 → BitVec 64) (key : ByteKeys.Key)
    (srcAligned : src.toNat % 8 = 0) (dstAligned : dst.toNat % 8 = 0)
    (srcFits : src.toNat + 32 < 2 ^ 64) (dstFits : dst.toNat + 32 < 2 ^ 64) (little : source.be = false)
    (sourceWords : MemoryBytes.WordView source src words) (sourceBytes : MemoryBytes.ByteView source src key)
    (mapped : ∀ limb : Fin 4, source.memaddrs (dst + BitVec.ofNat 64 (8 * limb.val))) :
    MemoryBytes.ByteView { source with memory := memory source.memory dst words } dst key := by
  have oldBytes := MemoryBytes.wordView_bytes source src words srcAligned srcFits little sourceWords
  have same := MemoryBytes.byteView_unique source src (WordKeys.key words) key oldBytes sourceBytes
  rw [← same]
  exact MemoryBytes.wordView_bytes _ dst words dstAligned dstFits little (word_view source dst words dstFits mapped)

end InitECandidate.Solver.WitnessRadix.Copy32

#print axioms InitECandidate.Solver.WitnessRadix.Copy32.word_view
#print axioms InitECandidate.Solver.WitnessRadix.Copy32.byte_view
