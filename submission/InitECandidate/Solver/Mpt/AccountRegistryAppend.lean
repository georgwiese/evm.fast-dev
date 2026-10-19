import InitECandidate.Solver.Mpt.AccountRegistry

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable

/-- A fresh account beyond the real old heap is separated from every live
table pool, regardless of their earlier relocations or allocation order. -/
theorem Registry.fresh_references {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (objects : ι → TableFamily.Object) (family : TableFamily.Model source cursor objects) (fresh : BitVec 64)
    (after : cursor≤fresh.toNat) (output : Output fresh) :
    ∀ offset : Nat,offset=40 ∨ offset=48 → TableFamily.Outside objects (fresh+BitVec.ofNat 64 offset) := by
  intro offset selected index
  have inside : offset<56 := by omega
  have number := output.slot_number fresh offset inside
  apply TableFootprint.Outside.of_regions _ _ (family.tables index).valid
  intro pool
  right
  rw [number]
  have := (family.tables index).earlier pool
  omega

/-- Register a genuinely produced fresh image. Its allocation and actual
image/separation evidence are explicit; no future helper model is assumed. -/
theorem Registry.append {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor nextCursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64)) (registry : Registry source cutoff cursor objects accounts)
    (fresh : BitVec 64) (image : Image source fresh) (after : cursor≤fresh.toNat) (above : cutoff≤fresh.toNat)
    (room : fresh.toNat+56≤nextCursor)
    (outside : ∀ offset : Nat,offset=40 ∨ offset=48 → TableFamily.Outside objects (fresh+BitVec.ofNat 64 offset)) :
    Registry source cutoff nextCursor objects (accounts++[fresh]) := by
  have notMember : fresh∉accounts := by
    intro member
    have := registry.before fresh member
    omega
  have membership (account : BitVec 64) (member : account∈accounts++[fresh]) : account∈accounts ∨ account=fresh := by simpa using member
  have forward : cursor≤nextCursor := by omega
  constructor
  · apply List.nodup_append.mpr
    refine ⟨registry.distinct,by simp,?_⟩
    intro first member second selected same
    have equal : second=fresh := by simpa using selected
    apply notMember
    rw [←same.trans equal]
    exact member
  · intro account member
    rcases membership account member with old | rfl
    · exact registry.images account old
    · exact ⟨image⟩
  · intro account member
    rcases membership account member with old | rfl
    · exact registry.above account old
    · exact above
  · intro account member
    rcases membership account member with old | rfl
    · have := registry.before account old; omega
    · exact room
  · intro first firstMember second secondMember different
    rcases membership first firstMember with firstOld | rfl
    · rcases membership second secondMember with secondOld | rfl
      · exact registry.separated first firstOld second secondOld different
      · exact Or.inl (Nat.le_trans (registry.before first firstOld) after)
    · rcases membership second secondMember with secondOld | rfl
      · exact Or.inr (Nat.le_trans (registry.before second secondOld) after)
      · exact (different rfl).elim
  · intro account member offset selected
    rcases membership account member with old | rfl
    · exact registry.referencesOutside account old offset selected
    · exact outside offset selected

theorem Registry.known_append (accounts : List (BitVec 64)) (fresh value : BitVec 64) (known : Registry.Known accounts value) :
    Registry.Known (accounts++[fresh]) value :=
  Registry.known_mono accounts (accounts++[fresh]) (fun account member=>List.mem_append.mpr (Or.inl member)) value known

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.fresh_references
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.append
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.known_append
