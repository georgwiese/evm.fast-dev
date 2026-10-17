import InitECandidate.Solver.WitnessRadix.UnaryBody
import InitECandidate.Solver.WitnessRadix.ScopedFrame
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.WitnessRadix.UnaryProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

/-- Complete actual counting scope for a unary radix level. The two scoped
counters are restored; only bit and clock change, and memory is preserved. -/
theorem count_scope_unary {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src start keys : BitVec 64) (keyFor : BitVec 64 → ByteKeys.Key)
    (input : List (BitVec 64)) (position : Nat)
    (inside : position < 256) (small : input.length < 2 ^ 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 input.length))))
    (rows : BuildCopy.Rows source.memory source.memaddrs src start 0 input)
    (views : ∀ ordinal ∈ input, MemoryBytes.ByteView source (keys + ordinal * 32#64) (keyFor ordinal))
    (unary : CountProgram.zeroCount keyFor position input = 0 ∨
      CountProgram.zeroCount keyFor position input = input.length)
    (enough : input.length ≤ source.clock) :
    evaluateHOLFiniteState source TerminalProgram.remainingCode =
      (some .continue, bind { source with clock := source.clock - input.length }
        "bit" (BitVec.ofNat 64 position + 1#64)) := by
  classical
  let zeroState := bind source "zeros" 0#64
  let entered := bind zeroState "i" 0#64
  have other (name : String) (notZero : ofString "zeros" ≠ ofString name)
      (notI : ofString "i" ≠ ofString name) :
      entered.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    dsimp only [entered, zeroState]
    rw [bind_lookup_other _ "i" name _ notI, bind_lookup_other source "zeros" name _ notZero]
  have index' : entered.locals.lookup (ofString "i") = some (.val (.word 0#64)) :=
    bind_lookup_same zeroState "i" 0#64
  have zero' : entered.locals.lookup (ofString "zeros") = some (.val (.word 0#64)) := by
    rw [bind_lookup_other zeroState "i" "zeros" 0#64 (by decide)]
    exact bind_lookup_same source "zeros" 0#64
  have views' : ∀ ordinal ∈ input, MemoryBytes.ByteView entered (keys + ordinal * 32#64) (keyFor ordinal) := by
    intro ordinal member
    exact MemoryBytes.byteView_of_fields source entered rfl rfl rfl _ _ (views ordinal member)
  obtain ⟨target, countRun, finalIndex, finalZeros, counterOther, frame⟩ :=
    CountProgram.loop_execute input entered src start keys 0#64 keyFor position 0 input.length inside small (Nat.zero_add _)
      ((other "src" (by decide) (by decide)).trans srcLocal)
      ((other "start" (by decide) (by decide)).trans startLocal)
      ((other "keys" (by decide) (by decide)).trans keysLocal)
      ((other "bit" (by decide) (by decide)).trans bitLocal) zero' index'
      ((other "count" (by decide) (by decide)).trans countLocal) rows views' enough
  have zerosTarget : target.locals.lookup (ofString "zeros") =
      some (.val (.word (BitVec.ofNat 64 (CountProgram.zeroCount keyFor position input)))) := by
    simpa using finalZeros
  have countTarget : target.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 input.length))) :=
    (counterOther _ (by decide) (by decide)).trans ((other "count" (by decide) (by decide)).trans countLocal)
  have bitTarget : target.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))) :=
    (counterOther _ (by decide) (by decide)).trans ((other "bit" (by decide) (by decide)).trans bitLocal)
  have unaryWord : BitVec.ofNat 64 (CountProgram.zeroCount keyFor position input) = 0#64 ∨
      BitVec.ofNat 64 (CountProgram.zeroCount keyFor position input) = BitVec.ofNat 64 input.length := by
    rcases unary with empty | full
    · exact Or.inl (by rw [empty])
    · exact Or.inr (congrArg (BitVec.ofNat 64) full)
  have afterRun := after_count_unary target _ _ _ zerosTarget countTarget bitTarget unaryWord
  have clockEq : target.clock = source.clock - input.length := congrArg (fun state => state.clock) frame
  have sequence : evaluateHOLFiniteState entered (.seq CountProgram.countLoop afterCount) =
      (some .continue, bind target "bit" (BitVec.ofNat 64 position + 1#64)) :=
    (StateSteps.next_sequence entered target CountProgram.countLoop afterCount countRun (by
      change target.clock ≤ source.clock
      omega)).trans afterRun
  have outside : ∀ query : MlS, query ≠ ofString "zeros" → query ≠ ofString "i" →
      target.locals.lookup query = source.locals.lookup query := by
    intro query notZero notI
    rw [counterOther query (Ne.symm notI) (Ne.symm notZero)]
    simp [entered, zeroState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, Ne.symm notZero, Ne.symm notI]
  have fields : emptyLocalsHOLFinite target =
      emptyLocalsHOLFinite { source with clock := source.clock - input.length } := by
    simpa only [entered, zeroState, QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite] using frame
  have restoredCounters : restore source "zeros" (restore zeroState "i" target) =
      { source with clock := source.clock - input.length } := by
    have savedI : zeroState.locals.lookup (ofString "i") = source.locals.lookup (ofString "i") :=
      bind_lookup_other source "zeros" "i" 0#64 (by decide)
    rw [restore_saved zeroState source target "i" savedI]
    exact restore_two_frame source target _ "zeros" "i" (by decide) outside rfl fields
  rw [remaining_shape, evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := (evaluateHOLFiniteState zeroState
      (.dec (ofString "i") .one (.const 0#64) (.seq CountProgram.countLoop afterCount)));
    (output.1, restore source "zeros" output.2)) = _
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := evaluateHOLFiniteState entered (.seq CountProgram.countLoop afterCount);
    (output.1, restore source "zeros" (restore zeroState "i" output.2))) = _
  rw [sequence]
  change (some (PanSemResultExact.continue : PanSemResultExact 64),
    restore source "zeros" (restore zeroState "i" (bind target "bit" (BitVec.ofNat 64 position + 1#64)))) = _
  rw [restore_bind_other zeroState target "i" "bit" _ (by decide),
    restore_bind_other source _ "zeros" "bit" _ (by decide), restoredCounters]

end InitECandidate.Solver.WitnessRadix.UnaryProgram

#print axioms InitECandidate.Solver.WitnessRadix.UnaryProgram.count_scope_unary
