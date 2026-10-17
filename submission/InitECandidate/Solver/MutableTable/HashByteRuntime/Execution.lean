import InitECandidate.Solver.MutableTable.HashByteRuntime.Loops

namespace InitECandidate.Solver.MutableTable.HashByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix
open MemeqByteRuntime (price)

/-- The actual unrolled paths are skipped for other small key widths, at
both pointer alignments. In particular this covers28/60-byte indexed keys. -/
theorem skip_front (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (len : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length))))
    (small : length ≤ 64) (not20 : length ≠ 20) (not32 : length ≠ 32) (not52 : length ≠ 52) :
    evaluateHOLFiniteState source front = (none, source) := by
  have different20 : BitVec.ofNat 64 length ≠ 20#64 := by
    intro equality
    have numeric := congrArg BitVec.toNat equality
    change length % 2 ^ 64 = 20 at numeric
    omega
  have different32 : BitVec.ofNat 64 length ≠ 32#64 := by
    intro equality
    have numeric := congrArg BitVec.toNat equality
    change length % 2 ^ 64 = 32 at numeric
    omega
  have different52 : BitVec.ofNat 64 length ≠ 52#64 := by
    intro equality
    have numeric := congrArg BitVec.toNat equality
    change length % 2 ^ 64 = 52 at numeric
    omega
  have foldAnd (a b : BitVec 64) : AndOp.and a (AndOp.and b (18446744073709551615#64)) = a &&& b := by
    change a &&& (b &&& BitVec.allOnes 64) = a &&& b
    rw [BitVec.and_allOnes]
  by_cases aligned : pointer &&& 7#64 = 0#64
  all_goals simp [front, Hash.afterLocals, Hash.body, Guest.guestFn_htab_hash, progToHOL, expToHOL, shapeToHOL,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, toExact,
    p, len, foldAnd, aligned, different20, different32, different52, valueIsWord, valueWord, wordOpHOL, wordOp,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, fixClockHOLFinite]

/-- Entire actual hash body for the small widths using its generic loops.
No helper or loop execution is a premise; every byte read is supplied as
physical input data, and all nonlocal fields are preserved. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat) (bytes : Nat → UInt8)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (len : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length))))
    (reads : ∀ index < length, @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (pointer + BitVec.ofNat 64 index) = some (bytes index))
    (small : length ≤ 64) (not20 : length ≠ 20) (not32 : length ≠ 32) (not52 : length ≠ 52)
    (enough : price length ≤ source.clock) :
    ∃ digest target, evaluateHOLFiniteState source Hash.body = (some (.returned (.val (.word digest))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - price length} := by
  let initialized := HashSized.initialized source
  let initial := WitnessRadix.QueryBranch.bind initialized "i" 0#64
  have initP : initialized.locals.lookup (ofString "p") = some (.val (.word pointer)) :=
    (HashSized.initialized_other source "p" (by decide) (by decide)).trans p
  have initLen : initialized.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (HashSized.initialized_other source "key_len" (by decide) (by decide)).trans len
  have inputs : Inputs initial pointer length bytes :=
    ⟨(bind_lookup_other _ "i" "p" _ (by decide)).trans initP,
     (bind_lookup_other _ "i" "key_len" _ (by decide)).trans initLen,
     ⟨0#64, (bind_lookup_other _ "i" "w" _ (by decide)).trans (HashSized.initialized_w source)⟩, reads⟩
  have initialH : initial.locals.lookup (ofString "h") = some (.val (.word 14695981039346656037#64)) :=
    (bind_lookup_other _ "i" "h" _ (by decide)).trans (HashSized.initialized_h source)
  obtain ⟨digest, run⟩ := blocks_execute initial pointer 14695981039346656037#64 length 0 bytes inputs
    (bind_lookup_same _ _ _) initialH small (by omega) (by change price (length - 0) ≤ source.clock; simpa only [Nat.sub_zero] using enough)
  have finalShape : emptyLocalsHOLFinite {initial with clock := initial.clock - price (length - 0)} =
      emptyLocalsHOLFinite {source with clock := source.clock - price length} := by simp only [Nat.sub_zero]; rfl
  rw [finalShape] at run
  have iRun := Input.ScalarScope.declare_execute initialized _ "i" (.const 0#64) 0#64 program _ rfl run
  have skipped := skip_front initialized pointer length initP initLen small not20 not32 not52
  have suffix := StateSteps.next_sequence initialized initialized front (.dec (ofString "i") .one (.const 0#64) program) skipped (Nat.le_refl _)
  rw [iRun, ← after_locals_shape] at suffix
  let hs := WitnessRadix.QueryBranch.bind source "h" 14695981039346656037#64
  have wRun := Input.ScalarScope.declare_execute hs _ "w" (.const 0#64) 0#64 Hash.afterLocals _ rfl suffix
  have hRun := Input.ScalarScope.declare_execute source _ "h" (.const 14695981039346656037#64) 14695981039346656037#64 _ _ rfl wRun
  refine ⟨digest, restore source "h" (restore hs "w" (restore initialized "i" (emptyLocalsHOLFinite {source with clock := source.clock - price length}))), ?_, ?_⟩
  · rw [Hash.body_shape]
    exact hRun
  · simp only [restore, emptyLocalsHOLFinite]

end InitECandidate.Solver.MutableTable.HashByteRuntime

#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.skip_front
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.execute
