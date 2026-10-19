import InitECandidate.Solver.Mpt.TrieWalkEffects
import InitECandidate.Solver.Input.LocalFlow
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
theorem loop_body_flow (key : String) (member : key ∈ (["nlen", "nibs"] : List String)) :
    Input.LocalFlow (ofString key) loopBody := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    simp only [loopBody, loop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL,
      List.map_cons, List.map_nil, Option.map_none]
    repeat first
      | apply Input.LocalFlow.seq
      | apply Input.LocalFlow.ite
      | apply Input.LocalFlow.dec
      | apply Input.LocalFlow.decCall
      | exact Input.LocalFlow.returned _
      | exact Input.LocalFlow.base (.assign _ _ (by decide))
      | exact Input.LocalFlow.base (.call none _ _ (by intro name impossible; cases impossible))
      | exact Input.LocalFlow.base .skip
      | (solve | decide)

theorem loop_body_no_continue (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source loopBody).1 ≠ some .continue :=
  (loop_body_flow "nlen" (by simp)).no_continue source

theorem loop_body_constants (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : evaluateHOLFiniteState source loopBody = (none, post)) :
    post.locals.lookup (ofString "nlen") = source.locals.lookup (ofString "nlen") ∧
    post.locals.lookup (ofString "nibs") = source.locals.lookup (ofString "nibs") :=
  ⟨(loop_body_flow "nlen" (by simp)).none_preserves source post run,
    (loop_body_flow "nibs" (by simp)).none_preserves source post run⟩

set_option maxRecDepth 10000 in
theorem leaf_stops : Input.NoFallthrough leaf := by
  simp only [leaf, leafGuard, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]
  apply Input.NoFallthrough.declared
  apply Input.NoFallthrough.sequence
  exact Input.NoFallthrough.returned _

theorem hash_passed_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString "k") = some (.val (.word tag)))
    (normal : evaluateHOLFiniteState source hashGuard = (none, post)) : tag ≠ 0#64 ∧ post = source := by
  by_cases zero : tag = 0#64
  · have failed : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "mpt_fail") [.const 2#64]) = (none, post) := by
      simpa [hash_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, cell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, zero] using normal
    exact (Fail.call_not_normal source post installed [.const 2#64] failed).elim
  · have actual : evaluateHOLFiniteState source hashGuard = (none, source) := by
      simp [hash_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, cell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, zero, evaluateHOLFiniteState_skip]
    exact ⟨zero, congrArg Prod.snd (normal.symm.trans actual)⟩

theorem leaf_skipped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (cell : source.locals.lookup (ofString "k") = some (.val (.word tag)))
    (normal : evaluateHOLFiniteState source leafGuard = (none, post)) : tag ≠ 1#64 ∧ post = source := by
  by_cases one : tag = 1#64
  · have stopped : evaluateHOLFiniteState source leaf = (none, post) := by
      simpa [leaf_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, cell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, one] using normal
    exact (leaf_stops source (congrArg Prod.fst stopped)).elim
  · have actual : evaluateHOLFiniteState source leafGuard = (none, source) := by
      simp [leaf_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, cell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, one, evaluateHOLFiniteState_skip]
    exact ⟨one, congrArg Prod.snd (normal.symm.trans actual)⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.loop_body_flow
#print axioms InitECandidate.Solver.Mpt.TrieWalk.loop_body_no_continue
#print axioms InitECandidate.Solver.Mpt.TrieWalk.loop_body_constants
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_stops
#print axioms InitECandidate.Solver.Mpt.TrieWalk.hash_passed_normal
#print axioms InitECandidate.Solver.Mpt.TrieWalk.leaf_skipped_normal
