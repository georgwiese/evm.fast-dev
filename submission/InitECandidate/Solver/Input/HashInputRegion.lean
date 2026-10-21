import InitECandidate.Solver.Input.SszHashProtected

namespace InitECandidate.Solver.Input.HashInput
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Agreement with actual copied/decoded memory on one fixed physical
input region. The upper frontier is fixed before hashing, not each nested
callee's later temporary heap. No future outcome or digest fact is included. -/
structure Frame (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) : Prop where
  words : ∀ query : BitVec 64,lower≤query.toNat → query.toNat<upper → current.memory query=origin.memory query

theorem Frame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) : Frame source source lower upper := ⟨by intro query low high; rfl⟩

theorem Frame.trans (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (first : Frame origin source lower upper) (next : Frame source target lower upper) : Frame origin target lower upper :=
  ⟨by intro query low high; exact (next.words query low high).trans (first.words query low high)⟩

theorem Frame.of_memory (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (current : Frame origin source lower upper) (same : target.memory=source.memory) : Frame origin target lower upper :=
  ⟨by intro query low high; rw [same]; exact current.words query low high⟩

theorem Frame.at_callee (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (lower upper : Nat)
    (current : Frame origin source lower upper) : Frame origin (callEntryStateHOLFinite source callee) lower upper := ⟨current.words⟩

theorem Frame.cell (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (current : Frame origin source lower upper) (query value : BitVec 64) (low : lower≤query.toNat) (high : query.toNat<upper)
    (stored : origin.memory query=.word value) : source.memory query=.word value := (current.words query low high).trans stored

/-- Only the actual initialized mutable workspace pointers must precede the
fixed input region. This states separation, not preservation or success. -/
structure Separation (stp accel chunk : BitVec 64) (lower : Nat) : Prop where
  state : stp.toNat+64≤lower
  accelerator : accel.toNat+96≤lower
  lengthChunk : chunk.toNat+32≤lower

theorem Separation.at_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel chunk zeros query : BitVec 64) (lower : Nat)
    (separation : Separation stp accel chunk lower) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (small : lower<2^64) (low : lower≤query.toNat) : SszHash.Protected source stp accel chunk zeros query :=
  ⟨workspace,CopyGeneral.Away.before stp query 64 lower separation.state small low,
    CopyGeneral.Away.before accel query 96 lower separation.accelerator small low,
    CopyGeneral.Away.before chunk query 32 lower separation.lengthChunk small low⟩

/-- Derive the next actual input agreement from ordinary per-word normal
memory contracts, applied only to the observed execution. -/
theorem Frame.after_normal (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (current : Frame origin source lower upper) (program : ProgHOL 64)
    (run : evaluateHOLFiniteState source program=(none,post))
    (preserves : ∀ query : BitVec 64,lower≤query.toNat → query.toNat<upper → evaluateHOLFiniteState source program=(none,post) → post.memory query=source.memory query) :
    Frame origin post lower upper :=
  current.trans origin source post lower upper ⟨by intro query low high; exact preserves query low high run⟩

end InitECandidate.Solver.Input.HashInput

#print axioms InitECandidate.Solver.Input.HashInput.Frame.refl
#print axioms InitECandidate.Solver.Input.HashInput.Frame.trans
#print axioms InitECandidate.Solver.Input.HashInput.Frame.of_memory
#print axioms InitECandidate.Solver.Input.HashInput.Frame.at_callee
#print axioms InitECandidate.Solver.Input.HashInput.Frame.cell
#print axioms InitECandidate.Solver.Input.HashInput.Separation.at_word
#print axioms InitECandidate.Solver.Input.HashInput.Frame.after_normal
