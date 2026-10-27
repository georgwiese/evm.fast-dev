import InitECandidate.Solver.Input.HeaderProgram
import InitECandidate.Solver.Input.LocalWord

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original outer-container bindings needed when the real decoder later
resumes witness parsing. These refer to the actual encoded input length. -/
structure OuterLocals (input : Guest.InputBlob) (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) : Prop where
  p : state.locals.lookup (ofString "p") = some (.val (.word (pointer + 2#64)))
  len : state.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2))))
  wit : state.locals.lookup (ofString "o_wit") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6))))
  lower : 16 ≤ Guest.GasLimit.le32 input 6
  upper : Guest.GasLimit.le32 input 6 ≤ input.length % 2^64 - 2

theorem OuterLocals.preserved {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer : BitVec 64} (actual : OuterLocals input source pointer)
    (kept : ∀ name ∈ ["p", "len", "o_wit"], target.locals.lookup (ofString name) = source.locals.lookup (ofString name)) :
    OuterLocals input target pointer :=
  ⟨(kept "p" (by simp)).trans actual.p, (kept "len" (by simp)).trans actual.len,
    (kept "o_wit" (by simp)).trans actual.wit, actual.lower, actual.upper⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.OuterLocals.preserved
