import InitECandidate.Solver.Input.StoreWordsNormal

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Normal stores whose actual expression has a bounded flattened width
retain every word outside that write interval, plus all nonmemory fields. -/
theorem store_bounded_normal {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address : BitVec 64) (width : Nat)
    (read : eval source destination = some (.val (.word address)))
    (bounded : ∀ value, eval source expression = some value → (flattenHOL value).length ≤ width)
    (normal : evaluateHOLFiniteState source (.store destination expression) = (none, target)) :
    target = {source with memory := target.memory} ∧
      ∀ query : BitVec 64, (∀ index < width, query ≠ address + BitVec.ofNat 64 (8 * index)) → target.memory query = source.memory query := by
  obtain ⟨value, memory, readValue, stored, same⟩ := store_at_normal source target destination expression address read normal
  have fits := bounded value readValue
  refine ⟨store_none_frame source target destination expression normal, ?_⟩
  intro query away
  rw [same]
  exact words_away (flattenHOL value) address query source.memaddrs source.memory memory stored (by intro index inside; exact away index (by omega))

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.store_bounded_normal
