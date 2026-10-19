import InitECandidate.Solver.Rlp.HeaderShortValues

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal enclosing return passes the actual nested canonical guard and
runs its continuation at the same state. No input-byte value is assumed. -/
theorem canonical_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (payload : BitVec 64)
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (continuation : ProgHOL 64) (value : ValueHOL 64) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.seq canonicalGuard continuation)=(some (.returned value),post)) :
    evaluateHOLFiniteState source continuation=(some (.returned value),post) := by
  let inner : ProgHOL 64 := .ite (.cmp .lower (.loadByte (.op .add [localVar "p",.const 1#64])) (.const 128#64)) (fail 4#64) .skip
  have equalRead : @evalHOLExact 64 Guest.HostMemory _ source.toExact
      (fun address=>Classical.propDecidable (source.memaddrs address)) (.cmp .equal (localVar "n") (.const 1#64))=
      some (.val (.word (if payload=1#64 then 1#64 else 0#64))) := by
    simp [evalHOLExact,localVar,toExact,payloadCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have dispatch : evaluateHOLFiniteState source canonicalGuard=
      if payload=1#64 then evaluateHOLFiniteState source inner else evaluateHOLFiniteState source .skip := by
    rw [canonicalGuard,evaluateHOLFiniteState_ite,equalRead]
    by_cases one : payload=1#64
    · simp only [if_pos one,if_neg (show (1#64 : BitVec 64)≠0 from by decide)]
      rfl
    · simp only [if_neg one,if_pos (show (0#64 : BitVec 64)=0 from rfl)]
  rw [evaluateHOLFiniteState_seq_line780,dispatch] at normal
  by_cases one : payload=1#64
  · rw [if_pos one] at normal
    have actual : evaluateHOLFiniteState source (.seq inner continuation)=(some (.returned value),post) := by
      rw [evaluateHOLFiniteState_seq_line780]
      exact normal
    exact (Fail.guard_return source post _ [.const 4#64] continuation value installed actual).2
  · rw [if_neg one,evaluateHOLFiniteState_skip] at normal
    exact normal

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.canonical_return
