import InitECandidate.Solver.GasBudget.JournalImage

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack PanSemStateFiniteExact MutableTable

theorem Image.of_above {ι : Type} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {objects : ι → TableFamily.Object} {base count cutoff : Nat} {entries : Nat → Entry ι}
    (image : Image source objects base count entries) (span : base + 32 * count < 2^64) (above : cutoff ≤ base)
    (domain : target.memaddrs = source.memaddrs)
    (words : ∀ query : BitVec 64, cutoff ≤ query.toNat → target.memory query = source.memory query) :
    Image target objects base count entries := by
  apply image.transfer domain (fun _ => rfl) (fun _ => rfl) _ image.separate
  intro index inside field
  have fieldBound := field.isLt
  apply words
  rw [entryAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.Image.of_above
