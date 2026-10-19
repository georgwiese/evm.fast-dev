import InitECandidate.Solver.Mpt.TrieWalkExtensionNormal

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Every outcome of the original extension costs at most fifteen source
call/loop ticks at a currently valid key position. An overlong path returns
before comparison; only its potentially visited prefix must be mapped. -/
theorem extension_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node nibs position size path : BitVec 64) (limit : Nat)
    (small : limit ≤ 64) (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (sizeMapped : source.memaddrs (node + 40#64)) (sizeStored : source.memory (node + 40#64) = .word size)
    (pathMapped : source.memaddrs (node + 32#64)) (pathStored : source.memory (node + 32#64) = .word path)
    (aFits : path.toNat + min size.toNat 64 < 2^64)
    (bFits : size.toNat ≤ limit - position.toNat → (nibs + position).toNat + size.toNat < 2^64)
    (leftMapped : ∀ offset < min size.toNat 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress path offset)))
    (rightMapped : size.toNat ≤ limit - position.toNat →
      ∀ offset < size.toNat, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress (nibs + position) offset)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one)) :
    source.clock - (evaluateHOLFiniteState source extension).2.clock ≤ 15 := by
  have sizeRead := node_field_read source node 40#64 size nodeCell sizeMapped sizeStored
  let entered := bind source "sl" size
  let output := evaluateHOLFiniteState entered (.seq extentGuard extensionCompare)
  have actual := Input.ScalarScope.declare_execute source output.2 "sl" (nodeField 40#64) size _ output.1 sizeRead rfl
  rw [← extension_shape] at actual
  rw [actual]
  change source.clock - (evaluateHOLFiniteState entered (.seq extentGuard extensionCompare)).2.clock ≤ 15
  have currentNode : entered.locals.lookup (ofString "node") = some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nodeCell
  have currentNibs : entered.locals.lookup (ofString "nibs") = some (.val (.word nibs)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nibsCell
  have currentPos : entered.locals.lookup (ofString "pos") = some (.val (.word position)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans posCell
  have currentLimit : entered.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans limitCell
  have currentSize : entered.locals.lookup (ofString "sl") = some (.val (.word size)) := bind_lookup_same _ _ _
  by_cases tooLong : BitVec.ofNat 64 limit - position < size
  · have guardRun : evaluateHOLFiniteState entered extentGuard = evaluateHOLFiniteState entered absent := by
      simp [extent_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact,
        remaining, localVar, currentPos, currentLimit, currentSize, valueIsWord, valueWord, wordOpHOL, wordOp,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, tooLong]
    rw [evaluateHOLFiniteState_seq_line780, guardRun]
    have clock : (evaluateHOLFiniteState entered absent).2.clock = source.clock :=
      Input.QuietClock.returned source.code _ entered rfl
    have stopped := absent_stops entered
    generalize completed : evaluateHOLFiniteState entered absent = result at clock stopped ⊢
    obtain ⟨result, target⟩ := result
    cases result with
    | none => exact (stopped rfl).elim
    | some result =>
      change source.clock - target.clock ≤ 15
      change target.clock = source.clock at clock
      omega
  · have guardRun : evaluateHOLFiniteState entered extentGuard = (none, entered) := by
      simp [extent_guard_shape, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact,
        remaining, localVar, currentPos, currentLimit, currentSize, valueIsWord, valueWord, wordOpHOL, wordOp,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, tooLong, evaluateHOLFiniteState_skip]
    obtain ⟨within, sizeSmall, addition, nextBounded, same⟩ :=
      extent_guard_numeral entered entered position size limit small bounded currentPos currentLimit currentSize guardRun
    have clipped : min size.toNat 64 = size.toNat := min_eq_left sizeSmall
    rw [clipped] at aFits leftMapped
    have bFits := bFits within
    have rightMapped := rightMapped within
    have args := compare_arguments_read entered node nibs position size path currentNode currentNibs currentPos currentSize pathMapped pathStored
    have cost := extension_compare_cost entered path (nibs + position) size.toNat sizeSmall aFits bFits leftMapped rightMapped code args
    have price := MemeqSmall.price_le_fourteen size.toNat sizeSmall
    rw [evaluateHOLFiniteState_seq_line780, guardRun]
    change entered.clock - (evaluateHOLFiniteState entered extensionCompare).2.clock ≤ 15
    omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_cost
