import InitECandidate.Solver.Mpt.TrieWalkControl
import InitECandidate.Solver.Input.SequenceStopped

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def unresolved : ProgHOL 64 := .call (some (none, none)) (ofString "mpt_fail") [.const 2#64]

/-- Exact original case selection, including the non-fallthrough hash and
leaf cases. This equality holds for every clock and every outcome. -/
theorem after_k_evaluate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString "k") = some (.val (.word tag))) :
    evaluateHOLFiniteState source afterK =
      if tag = 0#64 then evaluateHOLFiniteState source unresolved
      else if tag = 1#64 then evaluateHOLFiniteState source leaf
      else if tag = 2#64 then evaluateHOLFiniteState source extension
      else evaluateHOLFiniteState source branch := by
  have hashRead : evaluateHOLFiniteState source hashGuard =
      if tag = 0#64 then evaluateHOLFiniteState source unresolved else (none, source) := by
    simp [hash_guard_shape, unresolved, evaluateHOLFiniteState_ite, evalHOLExact, localVar, cell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, evaluateHOLFiniteState_skip]
  have leafRead : evaluateHOLFiniteState source leafGuard =
      if tag = 1#64 then evaluateHOLFiniteState source leaf else (none, source) := by
    simp [leaf_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, localVar, cell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, evaluateHOLFiniteState_skip]
  have stepRead : evaluateHOLFiniteState source nodeStep =
      if tag = 2#64 then evaluateHOLFiniteState source extension else evaluateHOLFiniteState source branch := by
    simp [node_step_shape, evaluateHOLFiniteState_ite, evalHOLExact, localVar, cell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases zero : tag = 0#64
  · rw [if_pos zero, hash_shape]
    have stopped : (evaluateHOLFiniteState source hashGuard).1 ≠ none := by
      rw [hashRead, if_pos zero]
      intro normal
      have run : evaluateHOLFiniteState source unresolved = (none, (evaluateHOLFiniteState source unresolved).2) :=
        Prod.ext normal rfl
      exact Fail.call_not_normal source _ installed [.const 2#64] run
    rw [Input.sequence_stopped source hashGuard afterHash stopped, hashRead, if_pos zero]
  · rw [if_neg zero, hash_shape, evaluateHOLFiniteState_seq_line780, hashRead, if_neg zero]
    change evaluateHOLFiniteState source afterHash = _
    by_cases one : tag = 1#64
    · rw [if_pos one, leaf_shape]
      have stopped : (evaluateHOLFiniteState source leafGuard).1 ≠ none := by
        rw [leafRead, if_pos one]
        exact leaf_stops source
      rw [Input.sequence_stopped source leafGuard nodeStep stopped, leafRead, if_pos one]
    · rw [if_neg one, leaf_shape, evaluateHOLFiniteState_seq_line780, leafRead, if_neg one]
      exact stepRead

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.after_k_evaluate
