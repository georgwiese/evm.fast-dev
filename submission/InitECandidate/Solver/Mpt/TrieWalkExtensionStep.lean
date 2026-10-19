import InitECandidate.Solver.Mpt.TrieWalkBranchNode

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem absent_stops : Input.NoFallthrough absent := Input.NoFallthrough.returned _

/-- A continuing original extension has passed the unsigned remaining-length
test. The test itself changes no state. -/
theorem extent_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (position limit size : BitVec 64)
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word limit)))
    (sizeCell : source.locals.lookup (ofString "sl") = some (.val (.word size)))
    (normal : evaluateHOLFiniteState source extentGuard = (none, post)) :
    size ≤ limit - position ∧ post = source := by
  by_cases tooLong : limit - position < size
  · have stopped : evaluateHOLFiniteState source absent = (none, post) := by
      simpa [extent_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact,
        remaining, localVar, posCell, limitCell, sizeCell, valueIsWord, valueWord, wordOpHOL, wordOp,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, tooLong] using normal
    exact (absent_stops source (congrArg Prod.fst stopped)).elim
  · have actual : evaluateHOLFiniteState source extentGuard = (none, source) := by
      simp [extent_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact,
        remaining, localVar, posCell, limitCell, sizeCell, valueIsWord, valueWord, wordOpHOL, wordOp,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, tooLong, evaluateHOLFiniteState_skip]
    refine ⟨?_, congrArg Prod.snd (normal.symm.trans actual)⟩
    change ¬ (limit - position).toNat < size.toNat at tooLong
    change size.toNat ≤ (limit - position).toNat
    omega

theorem extent_guard_numeral (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (position size : BitVec 64) (limit : Nat) (small : limit ≤ 64) (bounded : position.toNat ≤ limit)
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (sizeCell : source.locals.lookup (ofString "sl") = some (.val (.word size)))
    (normal : evaluateHOLFiniteState source extentGuard = (none, post)) :
    size.toNat ≤ limit - position.toNat ∧ size.toNat ≤ 64 ∧
      (position + size).toNat = position.toNat + size.toNat ∧
      (position + size).toNat ≤ limit ∧ post = source := by
  obtain ⟨within, same⟩ := extent_guard_normal source post position (BitVec.ofNat 64 limit) size posCell limitCell sizeCell normal
  have limitNumber : (BitVec.ofNat 64 limit).toNat = limit := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have order : position ≤ BitVec.ofNat 64 limit := by
    change position.toNat ≤ (BitVec.ofNat 64 limit).toNat
    rwa [limitNumber]
  change size.toNat ≤ (BitVec.ofNat 64 limit - position).toNat at within
  rw [BitVec.toNat_sub_of_le order, limitNumber] at within
  have sum : (position + size).toNat = position.toNat + size.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  exact ⟨within, by omega, sum, by omega, same⟩

theorem comparison_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (answer : BitVec 64)
    (cell : source.locals.lookup (ofString "eq2") = some (.val (.word answer)))
    (normal : evaluateHOLFiniteState source comparisonGuard = (none, post)) : answer ≠ 0#64 ∧ post = source := by
  by_cases zero : answer = 0#64
  · have stopped : evaluateHOLFiniteState source absent = (none, post) := by
      simpa [comparison_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, localVar, cell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, zero] using normal
    exact (absent_stops source (congrArg Prod.fst stopped)).elim
  · have actual : evaluateHOLFiniteState source comparisonGuard = (none, source) := by
      simp [comparison_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, localVar, cell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, zero, evaluateHOLFiniteState_skip]
    exact ⟨zero, congrArg Prod.snd (normal.symm.trans actual)⟩

theorem extension_advance_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node position size : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (sizeCell : source.locals.lookup (ofString "sl") = some (.val (.word size)))
    (normal : evaluateHOLFiniteState source extensionAdvance = (none, post)) :
    ∃ nextNode, eval (bind source "pos" (position + size)) (nodeField 48#64) = some (.val (.word nextNode)) ∧
      post = bind (bind source "pos" (position + size)) "node" nextNode := by
  rw [extension_advance_shape] at normal
  obtain ⟨middle, posRun, nodeRun⟩ := Input.sequence_none source post _ _ normal
  have read : eval source (.op .add [localVar "pos", localVar "sl"]) = some (.val (.word (position + size))) := by
    simp [eval, evalHOLExact, evalListHOLExact, localVar, posCell, sizeCell, valueIsWord, valueWord, wordOpHOL, wordOp]
  have middleEq := Input.assign_none source middle "pos" _ (position + size) read posRun
  subst middle
  have currentNode : (bind source "pos" (position + size)).locals.lookup (ofString "node") = some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nodeCell
  obtain ⟨nextNode, childRead, postEq⟩ := Input.scalar_assign_none _ post "node" (nodeField 48#64) node currentNode nodeRun
  exact ⟨nextNode, childRead, postEq⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.absent_stops
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extent_guard_normal
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extent_guard_numeral
#print axioms InitECandidate.Solver.Mpt.TrieWalk.comparison_guard_normal
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_advance_normal
