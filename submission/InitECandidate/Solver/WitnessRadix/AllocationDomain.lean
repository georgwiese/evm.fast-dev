import InitECandidate.Solver.WitnessRadix.LayoutMapping
import InitE.SourceSemantics

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact

/-- Every aligned word in the actual ordinary-memory arena is mapped by
the fixed challenge source domain. -/
theorem ordinary_mapped (pointer : BitVec 64)
    (lower : 2701131776 ≤ pointer.toNat) (upper : pointer.toNat < 33806089496)
    (aligned : pointer.toNat % 8 = 0) : InitE.ordinaryDomain pointer := by
  change Flapjack.Compiler.Backend.StackRemove.addresses 2701131776#64 3888119741 pointer
  apply (Flapjack.Compiler.Backend.StackRemove.mem_addresses _ _ _).mpr
  let index := (pointer.toNat - 2701131776) / 8
  have number : pointer.toNat = 2701131776 + 8 * index := by dsimp [index]; omega
  have bound : index < 3888119741 := by omega
  refine ⟨index, bound, ?_⟩
  change pointer = 2701131776#64 + BitVec.ofNat 64 index * 8#64
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  have encoded : (BitVec.ofNat 64 (index * 8)).toNat = index * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add_of_lt (by
    rw [encoded]
    change 2701131776 + index * 8 < 2 ^ 64
    omega), encoded]
  change pointer.toNat = 2701131776 + index * 8
  omega

/-- Actual source-domain mapping for every allocated layout word; memory
contents remain independent. No per-cell mapping oracle is needed. -/
theorem mapped_of_allocated {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (domain : source.memaddrs = InitE.ordinaryDomain)
    (lower : ∀ pool, 2701131776 ≤ (base layout pool).toNat)
    (upper : ∀ pool, (base layout pool).toNat + size layout pool ≤ 33806089496) :
    Mapped source layout := by
  intro pool offset aligned fits
  rw [domain]
  have bound := upper pool
  have nowrap : (base layout pool).toNat + offset < 2 ^ 64 := by omega
  have number := byteAddress_toNat (base layout pool) offset nowrap
  apply ordinary_mapped
  · change 2701131776 ≤ (byteAddress _ _).toNat
    rw [number]
    have := lower pool
    omega
  · change (byteAddress _ _).toNat < 33806089496
    rw [number]
    omega
  · exact byteAddress_aligned _ _ (valid.aligned pool) aligned nowrap

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.ordinary_mapped
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.mapped_of_allocated
