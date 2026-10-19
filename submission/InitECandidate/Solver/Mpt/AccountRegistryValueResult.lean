import InitECandidate.Solver.Mpt.AccountRegistry

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack PanSemStateFiniteExact MutableTable

/-- Combine a real cache origin with the provider's actual registration. -/
theorem Registry.known_of_cache (accounts next : List (BitVec 64)) (property : BitVec 64 → Prop)
    (retained : ∀ value,Registry.Known accounts value → Registry.Known next value)
    (cacheKnown : ∀ value,property value → Registry.Known accounts value)
    (value : BitVec 64) (origin : property value ∨ Registry.Known next value) : Registry.Known next value := by
  rcases origin with cached | produced
  · exact retained value (cacheKnown value cached)
  · exact produced

theorem Registry.known_of_caches (accounts next : List (BitVec 64)) (first second : BitVec 64 → Prop)
    (retained : ∀ value,Registry.Known accounts value → Registry.Known next value)
    (firstKnown : ∀ value,first value → Registry.Known accounts value)
    (secondKnown : ∀ value,second value → Registry.Known accounts value)
    (value : BitVec 64) (origin : first value ∨ second value ∨ Registry.Known next value) : Registry.Known next value := by
  rcases origin with cached | rest
  · exact retained value (firstKnown value cached)
  · exact Registry.known_of_cache accounts next second retained secondKnown value rest

theorem Registry.value_image {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64)) (registry : Registry source cutoff cursor objects accounts)
    (value : BitVec 64) (known : Registry.Known accounts value) : value=1#64 ∨ Nonempty (Image source value) := by
  rcases known with absent | member
  · exact Or.inl absent
  · exact Or.inr (registry.images value member)

theorem Registry.value_nonzero {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64)) (registry : Registry source cutoff cursor objects accounts)
    (value : BitVec 64) (known : Registry.Known accounts value) : value≠0#64 := by
  intro zero
  rcases known with absent | member
  · exact (by decide : (1#64 : BitVec 64)≠0#64) (absent.symm.trans zero)
  · obtain ⟨image⟩ := registry.images value member
    have lower := image.output.lower
    rw [zero] at lower
    change 2701131776≤0 at lower
    omega

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.known_of_cache
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.known_of_caches
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.value_image
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.value_nonzero
