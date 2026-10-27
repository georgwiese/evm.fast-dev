import InitECandidate.Solver.Input.CurrentDomain
import InitECandidate.Solver.WitnessRadix.ZeroConditions
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.NoneControl

namespace InitECandidate.Solver.Input.ZeroUnmapped
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

theorem block32_error {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (below : dst.toNat < InitE.sourceBase)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source Zero.block32 = (some .error, source) := by
  have addressRead : eval source (Copy32.address "dst" 0) = some (.val (.word dst)) := by
    simp [eval, Copy32.address, localVar, evalHOLExact, evalListHOLExact, dstLocal, indexLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have first := CurrentDomain.store_below_base_error source (Copy32.address "dst" 0) (.const 0#64)
    dst 0#64 domain below addressRead rfl
  rw [Zero.block32, evaluateHOLFiniteState_seq_line780]
  simp only [Zero.wordStore, first]

/-- At a real first word of at least32bytes below sourceBase, the actual
memzero loop either lacks its initial clock or fails at its first store. -/
theorem loop32_stopped {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat)
    (small : length + 32 < 2^64) (large : 32 ≤ length)
    (domain : source.memaddrs = InitE.ordinaryDomain) (below : dst.toNat < InitE.sourceBase)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    (evaluateHOLFiniteState source Zero.loop32).1 =
      some (if source.clock = 0 then .timeOut else .error) := by
  classical
  have read := Zero.condition_read source 0 length 32 small (by omega) (by omega) indexLocal lengthLocal
  simp only [Nat.zero_add, if_pos large] at read
  have failed := block32_error (decClockHOLFinite source) dst domain below dstLocal indexLocal
  rw [Zero.loop32_shape, evaluateHOLFiniteState_while_total, read]
  simp only [show (1#64) ≠ 0 from by decide, ↓reduceIte]
  by_cases zero : source.clock = 0
  · rw [if_pos zero, if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide)]
    simp only [if_pos zero]
  · rw [if_neg zero, failed, if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide)]
    simp only [if_neg zero]

/-- The literal current memzero body cannot return from such a scratch clear.
This is local control evidence; callers must still establish the actual
scratch pointer range and propagate the source outcome. -/
theorem body_no_return {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat)
    (small : length + 32 < 2^64) (large : 32 ≤ length) (aligned : dst.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (below : dst.toNat < InitE.sourceBase)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    ∀ value, (evaluateHOLFiniteState source Zero.body).1 ≠ some (.returned value) := by
  intro value returned
  let post := (evaluateHOLFiniteState source Zero.body).2
  have run : evaluateHOLFiniteState source Zero.body = (some (.returned value), post) := Prod.ext returned rfl
  rw [Zero.body_shape] at run
  let entered := bind source "i" 0#64
  obtain ⟨inner, actual, restored⟩ := declaration_return_word source post "i" (.const 0#64) 0#64
    (.seq (.ite Zero.alignment (.seq Zero.loop32 Zero.loopWord) .skip)
      (.seq Zero.loopBytes (.seq Zero.loopTail (.return (.const 0#64))))) value rfl run
  have left : LocalPrefix (ofString "n") Zero.loop32 := by
    rw [Zero.loop32_shape]
    exact .loop _ (.seq (.store _ _) (.seq (.store _ _) (.seq (.store _ _)
      (.seq (.store _ _) (.assign _ _ (by decide))))))
  have right : LocalPrefix (ofString "n") Zero.loopWord := by
    rw [Zero.loopWord_shape]
    exact .loop _ (.seq (.store _ _) (.assign _ _ (by decide)))
  have safe : LocalPrefix (ofString "n") (.ite Zero.alignment (.seq Zero.loop32 Zero.loopWord) .skip) :=
    .ite _ (.seq left right) .skip
  obtain ⟨middle, front, tail, saved⟩ := safe.normal_continue entered inner _ value actual
  have dstCell : entered.locals.lookup (ofString "dst") = some (.val (.word dst)) :=
    (bind_lookup_other source "i" "dst" 0#64 (by decide)).trans dstLocal
  have lengthCell : entered.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthLocal
  have alignedRead := Zero.alignment_read entered dst dstCell aligned
  simp only [eval] at alignedRead
  rw [evaluateHOLFiniteState_ite, alignedRead] at front
  simp only [show (1#64) ≠ 0 from by decide, ↓reduceIte] at front
  obtain ⟨next, first, rest⟩ := sequence_none entered middle Zero.loop32 Zero.loopWord front
  have stopped := loop32_stopped entered dst length small large domain below dstCell
    (bind_lookup_same _ _ _) lengthCell
  rw [first] at stopped
  cases stopped

end InitECandidate.Solver.Input.ZeroUnmapped

#print axioms InitECandidate.Solver.Input.ZeroUnmapped.block32_error
#print axioms InitECandidate.Solver.Input.ZeroUnmapped.loop32_stopped
#print axioms InitECandidate.Solver.Input.ZeroUnmapped.body_no_return
