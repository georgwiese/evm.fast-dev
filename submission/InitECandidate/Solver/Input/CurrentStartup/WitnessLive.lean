import InitECandidate.Solver.Input.Witness.OffsetProgram

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The five actual witness-slice bindings retained across its three list calls. -/
structure WitnessLive (input : Guest.InputBlob) (state : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) : Prop where
  wp : state.locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 (2 + Guest.GasLimit.le32 input 6))))
  wlen : state.locals.lookup (ofString "wlen") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6))))
  w0 : state.locals.lookup (ofString "w0") = some (.val (.word (Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6) 0)))
  w1 : state.locals.lookup (ofString "w1") = some (.val (.word (Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6) 1)))
  w2 : state.locals.lookup (ofString "w2") = some (.val (.word (Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6) 2)))

theorem WitnessLive.preserved {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer : BitVec 64} (actual : WitnessLive input source pointer)
    (kept : ∀ name ∈ ["wp", "wlen", "w0", "w1", "w2"],
      target.locals.lookup (ofString name) = source.locals.lookup (ofString name)) : WitnessLive input target pointer :=
  ⟨(kept "wp" (by simp)).trans actual.wp, (kept "wlen" (by simp)).trans actual.wlen,
    (kept "w0" (by simp)).trans actual.w0, (kept "w1" (by simp)).trans actual.w1, (kept "w2" (by simp)).trans actual.w2⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessLive.preserved
