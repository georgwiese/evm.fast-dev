import InitECandidate.Solver.GasBudget.Be64Normal
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.GasBudget.QuadWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite MemoryWriter

abbrev Clause := Nat × Fin 4
def address (offset : Nat) : ExpHOL 64 := if offset = 0 then localVar "out" else .op .add [localVar "out", .const (BitVec.ofNat 64 offset)]
def arguments (clause : Clause) : List (ExpHOL 64) := [address clause.1, U256Value.limb clause.2]
def program : List Clause → ProgHOL 64
  | [] => .return (.const 0#64)
  | clause :: rest => .seq (.call (some (none, none)) (ofString "st_be64") (arguments clause)) (program rest)
def clauses : List Clause := [(0, 3), (8, 2), (16, 1), (24, 0)]

theorem slow_shape : MemoryWriter.slow .quad = program clauses := by
  simp [MemoryWriter.slow, MemoryWriter.Kind.body, MemoryWriter.Kind.signature, MemoryWriter.Kind.original,
    Guest.guestFn_u256_to_be32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    program, clauses, arguments, address, U256Value.limb, localVar]
  rfl

theorem read_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : U256Value.Words) (clause : Clause)
    (pointerLocal : source.locals.lookup (ofString "out") = some (.val (.word pointer)))
    (valueLocal : source.locals.lookup (ofString "a") = some (U256Value.tuple words)) :
    evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) (arguments clause) =
      some [.val (.word (pointer + BitVec.ofNat 64 clause.1)), .val (.word (words clause.2))] := by
  have pointerRead : eval source (address clause.1) = some (.val (.word (pointer + BitVec.ofNat 64 clause.1))) := by
    by_cases zero : clause.1 = 0
    all_goals simp [address, zero, eval, evalHOLExact, evalListHOLExact, toExact, localVar, pointerLocal, valueIsWord, valueWord, wordOpHOL, wordOp]
  have limbRead := U256Value.limb_read source words clause.2 valueLocal
  simp only [eval] at pointerRead limbRead
  simp only [arguments, evalListHOLFinite, evalListHOLExact, pointerRead, limbRead]

set_option maxHeartbeats 1500000 in
theorem program_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : U256Value.Words)
    (commands : List Clause) (installed : Input.OriginalCode.Installed source.code)
    (pointerLocal : source.locals.lookup (ofString "out") = some (.val (.word pointer)))
    (valueLocal : source.locals.lookup (ofString "a") = some (U256Value.tuple words))
    (mapped : BytesMapped source pointer 32) (inside : ∀ clause ∈ commands, clause.1 + 8 ≤ 32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (program commands) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ paid : Nat, paid ≤ 3 * commands.length ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
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
    have safe : Input.LocalPrefix (ofString "out") (.call (some (none, none)) (ofString "st_be64") (arguments clause)) := .call none _ _ (by simp)
    obtain ⟨first, firstRun, tailRun, retained⟩ := safe.normal_continue source post (program rest) returned normal
    obtain ⟨firstPaid, firstBound, firstFits, firstClock, firstFrame, firstAway⟩ := be64_call_normal source first (pointer + BitVec.ofNat 64 clause.1) (words clause.2) installed
      (arguments clause) (read_arguments source pointer words clause pointerLocal valueLocal) (mapped.subrange clause.1 8 (inside clause (by simp))) firstRun
    have firstInstalled : Input.OriginalCode.Installed first.code := by rw [firstFrame]; exact installed
    have firstPointer : first.locals.lookup (ofString "out") = some (.val (.word pointer)) := by rw [firstFrame]; exact pointerLocal
    have firstValue : first.locals.lookup (ofString "a") = some (U256Value.tuple words) := by rw [firstFrame]; exact valueLocal
    have firstMapped : BytesMapped first pointer 32 := by rw [firstFrame]; exact mapped
    obtain ⟨value, restPaid, restBound, restFits, restClock, restFields, restAway⟩ := ih first post firstInstalled firstPointer firstValue firstMapped
      (by intro next member; exact inside next (by simp [member])) tailRun
    refine ⟨value, firstPaid + restPaid, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · rw [firstClock] at restFits; omega
    · rw [restClock, firstClock]; omega
    · rw [firstFrame] at restFields
      exact restFields
    · intro query away
      rw [restAway query away]
      exact firstAway query (away.subrange clause.1 8 (inside clause (by simp)))

theorem slow_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : U256Value.Words)
    (installed : Input.OriginalCode.Installed source.code)
    (pointerLocal : source.locals.lookup (ofString "out") = some (.val (.word pointer)))
    (valueLocal : source.locals.lookup (ofString "a") = some (U256Value.tuple words)) (mapped : BytesMapped source pointer 32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (MemoryWriter.slow .quad) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ paid : Nat, paid ≤ 12 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} ∧
      (∀ query, BytesAway pointer query 32 → post.memory query = source.memory query) := by
  rw [slow_shape] at normal
  exact program_normal source post pointer words clauses installed pointerLocal valueLocal mapped
    (by intro clause member; simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl <;> decide) returned normal

end InitECandidate.Solver.GasBudget.QuadWriter

#print axioms InitECandidate.Solver.GasBudget.QuadWriter.slow_shape
#print axioms InitECandidate.Solver.GasBudget.QuadWriter.program_normal
#print axioms InitECandidate.Solver.GasBudget.QuadWriter.slow_normal
