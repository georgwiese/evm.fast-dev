import InitECandidate.Solver.GasBudget.QuadWriterSlow
import InitECandidate.Solver.GasBudget.MemoryWriterWords
import InitECandidate.Solver.Input.AssignedQuietScalar

namespace InitECandidate.Solver.GasBudget.QuadWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite MemoryWriter

def assignedProgram : List Clause → ProgHOL 64
  | [] => .return (.const 0#64)
  | clause :: rest => .seq (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [U256Value.limb clause.2])
    (.seq (.store (address clause.1) (localVar "w")) (assignedProgram rest))

theorem bswap_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "bswap64") =
    some ([(ofString "x", .one)], ArithmeticEffects.Kind.bswap64.body, .one) := by
  simpa only [ArithmeticEffects.Kind.name, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original,
    Guest.guestFn_bswap64, ArithmeticEffects.Kind.body, paramToHOL, shapeToHOL, List.map_cons, List.map_nil]
    using OriginalCodeEnvironment.arithmetic code installed .bswap64

theorem read_address (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat)
    (pointerLocal : source.locals.lookup (ofString "out") = some (.val (.word pointer))) :
    eval source (address offset) = some (.val (.word (pointer + BitVec.ofNat 64 offset))) := by
  by_cases zero : offset = 0
  all_goals simp [address, zero, eval, evalHOLExact, evalListHOLExact, toExact, localVar, pointerLocal, valueIsWord, valueWord, wordOpHOL, wordOp]

set_option maxHeartbeats 1500000 in
theorem assigned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (commands : List Clause)
    (installed : Input.OriginalCode.Installed source.code)
    (pointerLocal : source.locals.lookup (ofString "out") = some (.val (.word pointer))) (mapped : BytesMapped source pointer 32)
    (aligned : pointer.toNat % 8 = 0) (inside : ∀ clause ∈ commands, clause.1 < 32 ∧ clause.1 % 8 = 0)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (assignedProgram commands) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ paid : Nat, paid ≤ commands.length ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} ∧
      (∀ query, BytesAway pointer query 32 → post.memory query = source.memory query) := by
  induction commands generalizing source post with
  | nil =>
    obtain ⟨read, postEq⟩ := Input.return_normal source post (.const 0#64) returned normal
    have value : returned = .val (.word 0#64) := (Option.some.inj read).symm
    refine ⟨value, 0, by simp, by simp, ?_, ?_, ?_⟩
    · rw [postEq]; simp [emptyLocalsHOLFinite]
    · rw [postEq]; rfl
    · intro query _; rw [postEq]; rfl
  | cons clause rest ih =>
    have safe : Input.LocalPrefix (ofString "out") (.call (some (some (.local, ofString "w"), none)) (ofString "bswap64") [U256Value.limb clause.2]) :=
      .call (some (ofString "w")) _ _ (by intro name equal; cases equal; decide)
    obtain ⟨first, firstRun, tailRun, retained⟩ := safe.normal_continue source post (.seq (.store (address clause.1) (localVar "w")) (assignedProgram rest)) returned normal
    have env := OriginalCodeEnvironment.arithmetic source.code installed
    obtain ⟨firstFits, word, firstEq⟩ := Input.assigned_quiet_scalar source first (ofString "w") (ofString "bswap64") (ofString "x") [U256Value.limb clause.2]
      ArithmeticEffects.Kind.bswap64.body (bswap_code source.code installed) (ArithmeticEffects.pure_bswap64 source.code env)
      (Input.ClockCost.of_quiet source.code _ (ArithmeticEffects.quiet_preserves .bswap64 source.code (by rfl))) firstRun
    have firstP := retained.trans pointerLocal
    have firstW : first.locals.lookup (ofString "w") = some (.val (.word word)) := by rw [firstEq]; simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have offset := inside clause (by simp)
    have storeMapped : first.memaddrs (pointer + BitVec.ofNat 64 clause.1) := by
      rw [firstEq]
      exact word_mapped mapped aligned clause.1 offset.2 offset.1
    have storeRun := StoreWord.execute first (address clause.1) (localVar "w") (pointer + BitVec.ofNat 64 clause.1) word
      (read_address first pointer clause.1 firstP) (by simp [eval, evalHOLExact, toExact, localVar, firstW]) storeMapped
    let stored := {first with memory := StoreWord.put first.memory (pointer + BitVec.ofNat 64 clause.1) word}
    rw [StateSteps.next_sequence first stored _ (assignedProgram rest) storeRun (Nat.le_refl _)] at tailRun
    have storedInstalled : Input.OriginalCode.Installed stored.code := by change Input.OriginalCode.Installed first.code; rw [firstEq]; exact installed
    have storedP : stored.locals.lookup (ofString "out") = some (.val (.word pointer)) := firstP
    have storedMapped : BytesMapped stored pointer 32 := by change BytesMapped first pointer 32; rw [firstEq]; exact mapped
    obtain ⟨value, restPaid, restBound, restFits, restClock, restFields, restAway⟩ :=
      ih stored post storedInstalled storedP storedMapped (by intro next member; exact inside next (by simp [member])) tailRun
    have firstClock : first.clock = source.clock - 1 := by rw [firstEq]; rfl
    have firstMemory : first.memory = source.memory := by rw [firstEq]; rfl
    refine ⟨value, 1 + restPaid, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · change restPaid ≤ first.clock at restFits
      rw [firstClock] at restFits
      omega
    · rw [restClock]
      change first.clock - restPaid = _
      rw [firstClock]
      omega
    · simpa only [stored, firstEq, Input.LocalEffects.erase, emptyLocalsHOLFinite, setVarHOLFinite] using restFields
    · intro query away
      rw [restAway query away]
      change StoreWord.put first.memory (pointer + BitVec.ofNat 64 clause.1) word query = _
      rw [StoreWord.put, if_neg (word_away away aligned clause.1 offset.2 offset.1), firstMemory]

end InitECandidate.Solver.GasBudget.QuadWriter

#print axioms InitECandidate.Solver.GasBudget.QuadWriter.assigned_normal
