import InitECandidate.Solver.Input.ProgressiveRound
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem updates_bound (code) : ClockCost.Bound code updates 0 := by
  unfold updates
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.of_quiet code _ (QuietClock.assign code _ _))
    (ClockCost.sequence code _ _ 0 0 (ClockCost.of_quiet code _ (QuietClock.assign code _ _)) (ClockCost.of_quiet code _ (QuietClock.assign code _ _)))

/-- Price the real original Merkle call and actual zero-cost updates from
the current capped count and physical arenas. Escaping failures are retained. -/
theorem after_cap_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (active : offset k<n) (actual : RoundState source p roots cursor zeros stp accel n k)
    (countLocal : source.locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 (min (4^k) (n-offset k))))))
    (mapped : Geometry p roots cursor zeros n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterCap=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*min (4^k) (n-offset k)+55*(2*k)+14 := by
  obtain ⟨round,depth,power,sizeBound,positive⟩ := round_geometry n k bounded active
  obtain ⟨inputArena,outputArena,bufferArena⟩ := pair_geometry p roots cursor zeros n k bounded active mapped
  have countBound := Nat.min_le_left (4^k) (n-offset k)
  have countNumber : (BitVec.ofNat 64 (min (4^k) (n-offset k))).toNat=min (4^k) (n-offset k) := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sizeNumber : (BitVec.ofNat 64 (4^k)).toNat=4^k := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have args := merkle_arguments source p roots (offset k) (min (4^k) (n-offset k)) (4^k) k
    actual.pointer actual.rootsLocal actual.position countLocal actual.sizeLocal actual.round
  have front : ∀ result target,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize") arguments)=(result,target) →
      result≠some .timeOut → source.clock-target.clock≤115*min (4^k) (n-offset k)+55*(2*k)+14 := by
    intro result target called notTimeout
    have cost := Merkle.call_cost source target (p+BitVec.ofNat 64 (32*offset k)) (BitVec.ofNat 64 (min (4^k) (n-offset k)))
      (BitVec.ofNat 64 (4^k)) cursor (roots+BitVec.ofNat 64 (32*k)) zeros stp accel (2*k) depth
      (by rw [countNumber,←power]; exact countBound) (by rw [sizeNumber,←power]) actual.workspace actual.heap actual.table
      (by rw [countNumber]; exact inputArena) (by rw [countNumber]; exact bufferArena) mapped.aligned outputArena mapped.tableArena
      (some none) arguments args result called notTimeout
    simpa only [countNumber] using cost
  have cost := ClockCost.sequence_terminating source post _ updates (115*min (4^k) (n-offset k)+55*(2*k)+14) 0 front
    (by intro middle normal result target continued notTimeout; have price:=updates_bound middle.code middle rfl; rw [continued] at price; exact price)
    result run notTimeout
  simpa only [Nat.add_zero] using cost

/-- Complete actual original progressive body step, including the lexical
remaining-count declaration and unsigned cap. No future success is assumed. -/
theorem step_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (active : offset k<n) (actual : RoundState source p roots cursor zeros stp accel n k)
    (mapped : Geometry p roots cursor zeros n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source step=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*min (4^k) (n-offset k)+55*(2*k)+14 := by
  obtain ⟨round,depth,power,sizeBound,positive⟩ := round_geometry n k bounded active
  rw [step_prefix source n (offset k) (4^k) (by omega) (by omega) (by omega) actual.count actual.position actual.sizeLocal] at run
  let entry := pairEntry source n (offset k) (4^k)
  let final := (evaluateHOLFiniteState entry afterCap).2
  have observed := congrArg Prod.fst run
  have remaining : evaluateHOLFiniteState entry afterCap=(result,final) := Prod.ext observed rfl
  have endpoint : post=restore source "cnt" final := (congrArg Prod.snd run).symm
  have price := after_cap_cost entry final p roots cursor zeros stp accel n k bounded active
    (RoundState.pair source p roots cursor zeros stp accel n k actual) (pair_entry_count source n (offset k) (4^k)) mapped result remaining notTimeout
  have clock : entry.clock=source.clock := (pair_entry_frame source n (offset k) (4^k)).2
  have postClock : post.clock=final.clock := by rw [endpoint]; rfl
  rw [postClock,←clock]
  exact price

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.updates_bound
#print axioms InitECandidate.Solver.Input.Progressive.after_cap_cost
#print axioms InitECandidate.Solver.Input.Progressive.step_cost
