import InitECandidate.Solver.Mpt.AccountRegistryExtension
import InitECandidate.Solver.Mpt.AccountRegistryAppend
import InitECandidate.Solver.MutableTable.FamilyAdvancePools
import InitECandidate.Solver.MutableTable.FamilyValues

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- A genuinely produced fresh account, actual heap advance and earlier-word
frame reconstruct all current tables and their occupied values and extend
the account registry. Creators supply their derived image and memory effect. -/
theorem Registry.after_fresh_account {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cutoff cursor nextCursor : Nat) (objects : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (fresh : BitVec 64) (image : Image target fresh) (after : cursor≤fresh.toNat) (above : cutoff≤fresh.toNat)
    (room : fresh.toNat+56≤nextCursor) (bounded : nextCursor≤33806089496) (aligned : nextCursor%8=0)
    (heap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 nextCursor))))
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (before : ∀ query : BitVec 64,query.toNat<cursor → target.memory query=source.memory query) :
    TableFamily.Model target nextCursor objects ∧ Registry target cutoff nextCursor objects (accounts++[fresh]) ∧
      TableFamily.ValuesHave target objects property ∧
      Registry.Extension accounts (accounts++[fresh]) cursor ∧
      Registry.Known (accounts++[fresh]) fresh := by
  have pools : ∀ index,MemoryModel.PoolFrame source.memory target.memory (objects index).kind (objects index).plan := by
    intro index pool offset inside
    apply before
    rw [number (objects index).kind _ (family.tables index).valid pool offset inside]
    have earlier := (family.tables index).earlier pool
    omega
  have nextFamily := family.advance_pools heap (by omega) bounded aligned domain endian pools
  have frame : TableFamily.PersistentFrame cutoff cursor objects objects source target :=
    ⟨fun query lower earlier outside=>⟨outside,before query earlier⟩⟩
  have retained := registry.framed source target cutoff cursor cursor objects objects accounts frame (Nat.le_refl _) domain
  have outside := Registry.fresh_outside source cursor objects family fresh after image.output
  have nextRegistry := retained.append target cutoff cursor nextCursor objects accounts fresh image after above room outside
  have nextValues : TableFamily.ValuesHave target objects property := by
    apply values.of_agreement source target objects property
    intro index slot inside member
    have valid := (family.tables index).valid
    have capNumber : (BitVec.ofNat 64 (objects index).plan.capacity).toNat=(objects index).plan.capacity := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (capacity_small (objects index).kind _ valid)]
    rw [capNumber] at inside
    rw [scaled_cell]
    exact pools index .values _ (word_offset_inside (objects index).kind _ .values slot.toNat (Or.inl rfl) inside)
  exact ⟨nextFamily,nextRegistry,nextValues,Registry.Extension.append accounts fresh cursor after,Or.inr (by simp)⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.after_fresh_account
