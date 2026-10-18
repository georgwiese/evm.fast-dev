import InitECandidate.Solver.MutableTable.DeleteDecision
import InitECandidate.Solver.MutableTable.DeleteMoveExecution

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem bind_move_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot : Nat)
    (locals : Move.Locals source kind plan hole slot) (name : String) (word : BitVec 64)
    (away : ∀ saved ∈ (["keys", "vals", "order", "order_pos", "klen", "stride", "i", "j"] : List String), ofString name ≠ ofString saved) :
    Move.Locals (WitnessRadix.QueryBranch.bind source name word) kind plan hole slot := by
  exact ⟨(bind_lookup_other _ name "keys" _ (away "keys" (by simp))).trans locals.keys,
    (bind_lookup_other _ name "vals" _ (away "vals" (by simp))).trans locals.values,
    (bind_lookup_other _ name "order" _ (away "order" (by simp))).trans locals.order,
    (bind_lookup_other _ name "order_pos" _ (away "order_pos" (by simp))).trans locals.position,
    (bind_lookup_other _ name "klen" _ (away "klen" (by simp))).trans locals.length,
    (bind_lookup_other _ name "stride" _ (away "stride" (by simp))).trans locals.stride,
    (bind_lookup_other _ name "i" _ (away "i" (by simp))).trans locals.hole,
    (bind_lookup_other _ name "j" _ (away "j" (by simp))).trans locals.slot⟩

/-- The original post-hash decision and optional complete movement, with
both declaration scopes restored. The hole either stays or becomes this
scan slot; the used-byte set and physical header remain unchanged. -/
theorem after_hash_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (moved : Fin count) (active : moved ≠ deleted)
    (locals : Move.Locals source kind plan hole (entries moved)) (value hash : BitVec 64)
    (valueCell : source.memory (cell plan .values (8 * entries moved)) = .word value)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (hashLocal : source.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (code : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ paid memory nextEntries nextHole, paid ≤ MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ∧
      evaluateHOLFiniteState source afterHash = (none, WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 nextHole)) ∧
      (nextHole = hole ∨ nextHole = entries moved) ∧
      Pending (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 nextHole)) kind plan count deleted nextEntries nextHole ∧
      MemoryModel.Header memory kind plan (BitVec.ofNat 64 count) := by
  let home := hash &&& (BitVec.ofNat 64 plan.capacity - 1#64)
  let homeState := WitnessRadix.QueryBranch.bind source "home" home
  let zeroState := WitnessRadix.QueryBranch.bind homeState "movable" 0#64
  let move := selected home (BitVec.ofNat 64 hole) (BitVec.ofNat 64 (entries moved))
  let flagWord : BitVec 64 := if move then 1#64 else 0#64
  let flagged := WitnessRadix.QueryBranch.bind homeState "movable" flagWord
  let tail : ProgHOL 64 := .ite (.cmp .notEqual (localVar "movable") (.const 0#64)) moveBranch .skip
  have fold (first second : BitVec 64) : AndOp.and first (AndOp.and second (18446744073709551615#64)) = first &&& second := by
    change first &&& (second &&& BitVec.allOnes 64) = first &&& second
    rw [BitVec.and_allOnes]
  have homeRead : eval source (.op .and [localVar "h", Find.mask]) = some (.val (.word home)) := by
    simp [eval, Find.mask, localVar, evalHOLExact, evalListHOLExact, toExact, hashLocal, capLocal, home, valueIsWord, valueWord, wordOpHOL, wordOp, fold]
  have homeLocals := bind_move_locals source kind plan hole (entries moved) locals "home" home
    (by intro saved member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have zeroLocals := Move.Locals.bind_flag homeState kind plan hole (entries moved) homeLocals 0#64
  have homeAtZero : zeroState.locals.lookup (ofString "home") = some (.val (.word home)) :=
    (bind_lookup_other _ "movable" "home" _ (by decide)).trans (bind_lookup_same _ _ _)
  have decisionRun : evaluateHOLFiniteState zeroState decision = (none, flagged) := by
    have actual := decision_execute zeroState home (BitVec.ofNat 64 hole) (BitVec.ofNat 64 (entries moved)) homeAtZero zeroLocals.hole zeroLocals.slot (bind_lookup_same _ _ _)
    simpa only [zeroState, JumpDest.bind_overwrite] using actual
  by_cases chosen : move = true
  · have flaggedLocal : flagged.locals.lookup (ofString "movable") = some (.val (.word 1#64)) := by
      simpa [flagged, flagWord, chosen] using bind_lookup_same homeState "movable" flagWord
    have flaggedLocals := Move.Locals.bind_flag homeState kind plan hole (entries moved) homeLocals flagWord
    have flaggedPending := Pending.of_fields source flagged kind plan count deleted entries hole pending rfl rfl rfl
    obtain ⟨paid, bounded, moveRun, nextPending, nextHeader⟩ := Move.execute_pending flagged kind plan valid domain count deleted entries hole flaggedPending moved active flaggedLocals value valueCell header code enough
    let memory := Move.memory source.memory source.be kind plan hole (entries moved) moved.val value
    let canonical := {source with memory := memory, clock := source.clock - paid}
    let canonicalHome := WitnessRadix.QueryBranch.bind canonical "home" home
    let target := WitnessRadix.QueryBranch.bind {flagged with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 (entries moved))
    have branchRun : evaluateHOLFiniteState flagged tail = (none, target) := by
      simp [tail, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, flaggedLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, moveRun] <;> rfl
    have inner : evaluateHOLFiniteState zeroState (.seq decision tail) = (none, target) := by
      rw [StateSteps.next_sequence zeroState flagged decision tail decisionRun (Nat.le_refl _), branchRun]
    have movableRun := Input.ScalarScope.declare_execute homeState _ "movable" (.const 0#64) 0#64 (.seq decision tail) none rfl inner
    have homeRun := Input.ScalarScope.declare_execute source _ "home" (.op .and [localVar "h", Find.mask]) home
      (.dec (ofString "movable") .one (.const 0#64) (.seq decision tail)) none homeRead movableRun
    have targetEq : target = WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind canonicalHome "movable" flagWord) "i" (BitVec.ofNat 64 (entries moved)) := rfl
    have restored : restore source "home" (restore homeState "movable" target) = WitnessRadix.QueryBranch.bind canonical "i" (BitVec.ofNat 64 (entries moved)) := by
      rw [targetEq, restore_bind_other homeState (WitnessRadix.QueryBranch.bind canonicalHome "movable" flagWord) "movable" "i" _ (by decide)]
      change restore source "home" (WitnessRadix.QueryBranch.bind (restore canonicalHome "movable" (WitnessRadix.QueryBranch.bind canonicalHome "movable" flagWord)) "i" _) = _
      rw [restore_bound, restore_bind_other source canonicalHome "home" "i" _ (by decide)]
      change WitnessRadix.QueryBranch.bind (restore canonical "home" (WitnessRadix.QueryBranch.bind canonical "home" home)) "i" _ = _
      rw [restore_bound]
    refine ⟨paid, memory, Function.update entries moved hole, entries moved, bounded, ?_, Or.inr rfl, ?_, nextHeader⟩
    · simpa only [afterHash, restored] using homeRun
    · exact Pending.of_fields _ _ kind plan count deleted _ _ nextPending rfl rfl rfl
  · have flaggedLocal : flagged.locals.lookup (ofString "movable") = some (.val (.word 0#64)) := by
      simpa [flagged, flagWord, chosen] using bind_lookup_same homeState "movable" flagWord
    have flaggedEq : flagged = zeroState := by simp [flagged, flagWord, chosen, zeroState]
    have branchRun : evaluateHOLFiniteState flagged tail = (none, flagged) := by
      simp [tail, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, flaggedLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have inner : evaluateHOLFiniteState zeroState (.seq decision tail) = (none, flagged) := by
      rw [StateSteps.next_sequence zeroState flagged decision tail decisionRun (Nat.le_refl _), branchRun]
    have movableRun := Input.ScalarScope.declare_execute homeState _ "movable" (.const 0#64) 0#64 (.seq decision tail) none rfl inner
    have homeRun := Input.ScalarScope.declare_execute source _ "home" (.op .and [localVar "h", Find.mask]) home
      (.dec (ofString "movable") .one (.const 0#64) (.seq decision tail)) none homeRead movableRun
    have unchanged := JumpDest.bind_existing source "i" (BitVec.ofNat 64 hole) locals.hole
    refine ⟨0, source.memory, entries, hole, Nat.zero_le _, ?_, Or.inl rfl, ?_, header⟩
    · simpa only [afterHash, flaggedEq, zeroState, homeState, restore_bound, Nat.sub_zero, unchanged] using homeRun
    · exact Pending.of_fields source _ kind plan count deleted entries hole pending rfl rfl rfl

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.after_hash_execute
