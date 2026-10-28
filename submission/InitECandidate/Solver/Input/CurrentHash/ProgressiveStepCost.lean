import InitECandidate.Solver.Input.CurrentHash.ProgressiveRound
import InitECandidate.Solver.Input.CurrentHash.MerkleCallCost
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveStepCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Progressive ProgressiveRound

theorem updates_cost (code) : ClockCost.Bound code updates 0 := by
  unfold updates
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _)
    (ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _) (ClockCost.assign code _ _))

/-- The actual capped Merkle call's count and limit come from this same current
round. Pointer mapping and successful hashing are unnecessary for its price. -/
theorem merkle_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (bounded : n ≤ 134217728) (active : offset k < n) (data : Round source p roots n k)
    (count : source.locals.lookup (ofString "cnt") = some (.val (.word (BitVec.ofNat 64 (min (4^k) (n-offset k))))))
    (installed : OriginalCode.Installed source.code) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "merkleize") arguments) = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*min (4^k) (n-offset k) + 4*(2*k) + 49 := by
  obtain ⟨round, depth, power, sizeBound, positive⟩ := round_geometry n k bounded active
  have countBound := Nat.min_le_left (4^k) (n-offset k)
  have countNumber : (BitVec.ofNat 64 (min (4^k) (n-offset k))).toNat = min (4^k) (n-offset k) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have sizeNumber : (BitVec.ofNat 64 (4^k)).toNat = 4^k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have args := merkle_arguments source p roots (offset k) (min (4^k) (n-offset k)) (4^k) k
    data.pointer data.rootsLocal data.position count data.sizeLocal data.round
  have priced := MerkleCallCost.cost source post (p + BitVec.ofNat 64 (32*offset k)) (BitVec.ofNat 64 (min (4^k) (n-offset k)))
    (BitVec.ofNat 64 (4^k)) (roots + BitVec.ofNat 64 (32*k)) (2*k) (by omega)
    (by rw [countNumber, ←power]; exact countBound) (by rw [sizeNumber, ←power]) installed (some none) arguments args result actual notTimeout
  simpa only [countNumber] using priced

theorem after_cap_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (bounded : n ≤ 134217728) (active : offset k < n) (data : Round source p roots n k)
    (count : source.locals.lookup (ofString "cnt") = some (.val (.word (BitVec.ofNat 64 (min (4^k) (n-offset k))))))
    (installed : OriginalCode.Installed source.code) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source afterCap = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*min (4^k) (n-offset k) + 4*(2*k) + 49 := by
  rw [afterCap] at actual
  have priced := ClockCost.sequence_terminating source post _ updates (88*min (4^k) (n-offset k) + 4*(2*k) + 49) 0
    (fun result target evaluated notTimeout => merkle_cost source target p roots n k bounded active data count installed result evaluated notTimeout)
    (by intro middle continued result target evaluated notTimeout
        have same := updates_cost middle.code middle rfl
        rw [evaluated] at same
        exact same) result actual notTimeout
  simpa only [Nat.add_zero] using priced

/-- One actual progressive body, including its declaration/cap header and any
failed Merkle path. Only the same observed outcome is restricted to non-timeout. -/
theorem cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (bounded : n ≤ 134217728) (active : offset k < n) (data : Round source p roots n k)
    (installed : OriginalCode.Installed source.code) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source step = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*min (4^k) (n-offset k) + 4*(2*k) + 49 := by
  obtain ⟨round, depth, power, sizeBound, positive⟩ := round_geometry n k bounded active
  rw [step_prefix source n (offset k) (4^k) (by omega) (by omega) (by omega) data.count data.position data.sizeLocal] at actual
  let entry := pairEntry source n (offset k) (4^k)
  let final := (evaluateHOLFiniteState entry afterCap).2
  have observed := congrArg Prod.fst actual
  have remaining : evaluateHOLFiniteState entry afterCap = (result, final) := Prod.ext observed rfl
  have endpoint : post = restore source "cnt" final := (congrArg Prod.snd actual).symm
  have frame := pair_entry_frame source n (offset k) (4^k)
  have entryCode : OriginalCode.Installed entry.code := by
    have same := congrArg PanSemStateFiniteExact.code frame.1
    change entry.code = source.code at same
    rw [same]
    exact installed
  have priced := after_cap_cost entry final p roots n k bounded active data.pair (pair_entry_count source n (offset k) (4^k)) entryCode result remaining notTimeout
  have clock : entry.clock = source.clock := frame.2
  rw [endpoint]
  change source.clock - final.clock ≤ _
  rw [←clock]
  exact priced

end InitECandidate.Solver.Input.CurrentHash.ProgressiveStepCost

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveStepCost.updates_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveStepCost.merkle_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveStepCost.after_cap_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveStepCost.cost
