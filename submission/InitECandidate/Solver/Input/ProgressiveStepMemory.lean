import InitECandidate.Solver.Input.ProgressiveStepNormal
import InitECandidate.Solver.Input.MerkleMemory

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real capped chunk call and the original three updates preserve a
word outside the root array, below temporary storage and outside SHA buffers. -/
theorem after_cap_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p roots cursor zeros stp accel chunk query : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (active : offset k<n)
    (actual : RoundState source p roots cursor zeros stp accel n k)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (countLocal : source.locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 (min (4^k) (n-offset k))))))
    (mapped : Geometry p roots cursor zeros n) (below : query.toNat<cursor.toNat)
    (rootsAway : CopyGeneral.Away roots query 768)
    (run : evaluateHOLFiniteState source afterCap=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨round,depth,power,sizeBound,positive⟩ := round_geometry n k bounded active
  obtain ⟨inputArena,outArena,bufferArena⟩ := pair_geometry p roots cursor zeros n k bounded active mapped
  have countBound := Nat.min_le_left (4^k) (n-offset k)
  have countNumber : (BitVec.ofNat 64 (min (4^k) (n-offset k))).toNat=min (4^k) (n-offset k) := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sizeNumber : (BitVec.ofNat 64 (4^k)).toNat=4^k := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨middle,called,continued⟩ := sequence_none source post _ updates run
  have frame := Merkle.call_memory source middle (p+BitVec.ofNat 64 (32*offset k))
    (BitVec.ofNat 64 (min (4^k) (n-offset k))) (BitVec.ofNat 64 (4^k)) cursor
    (roots+BitVec.ofNat 64 (32*k)) stp accel chunk zeros query (2*k) depth
    (by rw [countNumber,←power]; exact countBound) (by rw [sizeNumber,←power]) protection actual.heap
    (by rw [countNumber]; exact inputArena) (by rw [countNumber]; exact bufferArena) mapped.aligned outArena below
    (CopyGeneral.Away.subrange roots query 768 (32*k) 32 rootsAway (by omega)) arguments
    (merkle_arguments source p roots (offset k) (min (4^k) (n-offset k)) (4^k) k actual.pointer actual.rootsLocal actual.position countLocal actual.sizeLocal actual.round) called
  have current := round_after_merkle source middle p roots cursor zeros stp accel n k bounded active actual countLocal mapped called
  have updatesRun := updates_execute middle (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k) current.position current.sizeLocal current.round
  rw [continued] at updatesRun
  have endpoint : post=advanced middle (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k) := congrArg Prod.snd updatesRun
  rw [endpoint]
  exact frame

/-- Original progressive cnt declaration and clamp do not alter memory;
the actual normal chunk call supplies the complete step frame. -/
theorem step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p roots cursor zeros stp accel chunk query : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (active : offset k<n)
    (actual : RoundState source p roots cursor zeros stp accel n k)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (mapped : Geometry p roots cursor zeros n) (below : query.toNat<cursor.toNat)
    (rootsAway : CopyGeneral.Away roots query 768)
    (run : evaluateHOLFiniteState source step=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨round,depth,power,sizeBound,positive⟩ := round_geometry n k bounded active
  rw [step_prefix source n (offset k) (4^k) (by omega) (by omega) (by omega) actual.count actual.position actual.sizeLocal] at run
  let entry := pairEntry source n (offset k) (4^k)
  let final := (evaluateHOLFiniteState entry afterCap).2
  have observed := congrArg Prod.fst run
  have remaining : evaluateHOLFiniteState entry afterCap=(none,final) := Prod.ext observed rfl
  have endpoint : post=restore source "cnt" final := (congrArg Prod.snd run).symm
  have frozen := (pair_entry_frame source n (offset k) (4^k)).1
  have entryProtection := SszHash.Protected.of_fields source entry stp accel chunk zeros query protection
    (by have h:=congrArg PanSemStateFiniteExact.code frozen; exact h) (by have h:=congrArg PanSemStateFiniteExact.memaddrs frozen; exact h)
    (by intro key other; have h:=congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory=>s.globals.lookup key) frozen; exact h)
  have frame := after_cap_memory entry final p roots cursor zeros stp accel chunk query n k bounded active
    (RoundState.pair source p roots cursor zeros stp accel n k actual) entryProtection
    (pair_entry_count source n (offset k) (4^k)) mapped below rootsAway remaining
  have entryMemory : entry.memory query=source.memory query := by have h:=congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory=>s.memory query) frozen; exact h
  rw [endpoint]
  exact frame.trans entryMemory

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.after_cap_memory
#print axioms InitECandidate.Solver.Input.Progressive.step_memory
