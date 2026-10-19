import InitECandidate.Solver.Mpt.TrieWalkStepProgram
import InitECandidate.Solver.Input.CounterFlow
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.EraseClock

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
theorem branch_terminal_stops : Input.NoFallthrough branchTerminal := by
  simp only [branchTerminal, branchGuard, branch, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body,
    Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]
  apply Input.NoFallthrough.declared
  apply Input.NoFallthrough.sequence
  exact Input.NoFallthrough.returned _

theorem branch_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (position limit : BitVec 64)
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word limit)))
    (normal : evaluateHOLFiniteState source branchGuard = (none, post)) : position ≠ limit ∧ post = source := by
  by_cases same : position = limit
  · have stopped : evaluateHOLFiniteState source branchTerminal = (none, post) := by
      simpa [branch_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, posCell, limitCell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, same] using normal
    exact (branch_terminal_stops source (congrArg Prod.fst stopped)).elim
  · have actual : evaluateHOLFiniteState source branchGuard = (none, source) := by
      simp [branch_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, posCell, limitCell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, same, evaluateHOLFiniteState_skip]
    exact ⟨same, congrArg Prod.snd (normal.symm.trans actual)⟩

set_option maxRecDepth 10000 in
theorem branch_advances : Input.CounterFlow.Advances (ofString "pos") 1 branchAdvance := by
  have nodeSafe : Input.LocalPrefix (ofString "pos") branchNode := by
    simp only [branchNode, branchAdvance, branch, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body,
      Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]
    exact .assign _ _ (by decide)
  have increment : Input.CounterFlow.Advances (ofString "pos") 1 branchPosition := by
    simpa only [branchPosition, addConst, localVar] using Input.CounterFlow.increment (ofString "pos")
  rw [branch_advance_shape]
  exact Input.CounterFlow.sequence (ofString "pos") branchNode branchPosition 0 1
    (Input.CounterFlow.preserved (ofString "pos") branchNode nodeSafe) increment

set_option maxRecDepth 10000 in
theorem branch_effects (code) : Input.LocalEffects.Preserves code branch ∧ Input.QuietClock.Preserves code branch := by
  constructor
  · simp only [branch, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
      progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]
    repeat first
      | apply Input.LocalEffects.sequence
      | apply Input.LocalEffects.declared
      | apply Input.LocalEffects.conditional
      | exact Input.LocalEffects.assign code _ _
      | exact Input.LocalEffects.returned code _
      | exact Input.LocalEffects.skip code
  · simp only [branch, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body, Guest.guestFn_trie_walk,
      progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]
    repeat first
      | apply Input.QuietClock.sequence
      | apply Input.QuietClock.declared
      | apply Input.QuietClock.conditional
      | exact Input.QuietClock.assign code _ _
      | exact Input.QuietClock.returned code _
      | exact Input.QuietClock.skip code

/-- Actual nonterminal branch visits consume one key nibble, without word
wrapping or source call clocks. All physical nonlocal fields are retained. -/
theorem branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (position : BitVec 64) (limit : Nat)
    (limitSmall : limit ≤ 64) (bounded : position.toNat ≤ limit)
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (normal : evaluateHOLFiniteState source branch = (none, post)) :
    position.toNat < limit ∧ post.locals.lookup (ofString "pos") = some (.val (.word (position + 1#64))) ∧
      (position + 1#64).toNat = position.toNat + 1 ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite source := by
  have run := normal
  rw [branch_shape] at run
  obtain ⟨middle, guardRun, advanceRun⟩ := Input.sequence_none source post branchGuard branchAdvance run
  obtain ⟨different, middleEq⟩ := branch_guard_normal source middle position (BitVec.ofNat 64 limit) posCell limitCell guardRun
  subst middle
  have limitNumber : (BitVec.ofNat 64 limit).toNat = limit := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have differentNumber : position.toNat ≠ limit := by
    intro same
    apply different
    apply BitVec.eq_of_toNat_eq
    rw [limitNumber, same]
  have active : position.toNat < limit := by omega
  have advanced := branch_advances source post position posCell advanceRun
  have number : (position + 1#64).toNat = position.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change position.toNat + 1 < 2^64; omega)
  have fields := (branch_effects source.code).1 source rfl
  have clock := (branch_effects source.code).2 source rfl
  rw [normal] at fields clock
  exact ⟨active, advanced, number, Input.LocalEffects.same_clock fields clock⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_terminal_stops
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_guard_normal
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_advances
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_effects
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_normal
