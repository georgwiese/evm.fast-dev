import InitECandidate.Solver.GasBudget.QuadWriterAssignments
import InitECandidate.Solver.Input.PricedScalarPrefix
import InitECandidate.Solver.Input.KnownUnaryPrefix

namespace InitECandidate.Solver.GasBudget.QuadWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite MemoryWriter

def tailClauses : List Clause := [(8, 2), (16, 1), (24, 0)]
def fastTail : ProgHOL 64 := .seq (.store (localVar "out") (localVar "w")) (assignedProgram tailClauses)

theorem fast_shape : MemoryWriter.fast .quad = .decCall (ofString "w") .one (ofString "bswap64") [U256Value.limb 3] fastTail := by
  simp [MemoryWriter.fast, MemoryWriter.Kind.body, MemoryWriter.Kind.signature, MemoryWriter.Kind.original,
    Guest.guestFn_u256_to_be32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    fastTail, assignedProgram, tailClauses, address, U256Value.limb, localVar]
  rfl

set_option maxHeartbeats 1500000 in
theorem fast_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (pointerLocal : source.locals.lookup (ofString "out") = some (.val (.word pointer)))
    (mapped : BytesMapped source pointer 32) (aligned : pointer.toNat % 8 = 0)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (MemoryWriter.fast .quad) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ paid : Nat, paid ≤ 4 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} ∧
      (∀ query, BytesAway pointer query 32 → post.memory query = source.memory query) := by
  rw [fast_shape] at normal
  have env := OriginalCodeEnvironment.arithmetic source.code installed
  obtain ⟨firstPaid, word, ready, inner, positive, bound, fits, readyEq, fields, run, scopeEq⟩ :=
    Input.PricedScalarPrefix.normal source post "w" (ofString "bswap64") [U256Value.limb 3] fastTail
      ArithmeticEffects.Kind.bswap64.signature.1 ArithmeticEffects.Kind.bswap64.body ArithmeticEffects.Kind.bswap64.signature.2.2 0
      (env .bswap64) (ArithmeticEffects.pure_bswap64 source.code env)
      (Input.ClockCost.of_quiet source.code _ (ArithmeticEffects.quiet_preserves .bswap64 source.code (by rfl))) returned normal
  have paidEq : firstPaid = 1 := by omega
  subst firstPaid
  have readyPointer := (Input.KnownUnaryPrefix.lookup_other readyEq "out" (by decide)).trans pointerLocal
  have readyWord := Input.KnownUnaryPrefix.lookup_same readyEq
  have pointerMapped : source.memaddrs pointer := by simpa using word_mapped mapped aligned 0 (by decide) (by decide)
  have readyMapped : ready.memaddrs pointer := by rw [readyEq]; exact pointerMapped
  have storeRun := StoreWord.execute ready (localVar "out") (localVar "w") pointer word
    (by simp [eval, evalHOLExact, toExact, localVar, readyPointer]) (by simp [eval, evalHOLExact, toExact, localVar, readyWord]) readyMapped
  let stored := {ready with memory := StoreWord.put ready.memory pointer word}
  rw [fastTail, StateSteps.next_sequence ready stored _ (assignedProgram tailClauses) storeRun (Nat.le_refl _)] at run
  have storedInstalled : Input.OriginalCode.Installed stored.code := by change Input.OriginalCode.Installed ready.code; rw [readyEq]; exact installed
  have storedMapped : BytesMapped stored pointer 32 := by change BytesMapped ready pointer 32; rw [readyEq]; exact mapped
  obtain ⟨value, restPaid, restBound, restFits, restClock, restFields, restAway⟩ :=
    assigned_normal stored inner pointer tailClauses storedInstalled readyPointer storedMapped aligned
      (by intro clause member; simp only [tailClauses, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> decide) returned run
  have readyClock : ready.clock = source.clock - 1 := by rw [readyEq]; rfl
  have memory := Input.LocalEffects.memory_of_erase source ready fields
  have postMemory : post.memory = inner.memory := by rw [scopeEq]; rfl
  refine ⟨value, 1 + restPaid, by change restPaid ≤ 3 at restBound; omega, ?_, ?_, ?_, ?_⟩
  · change restPaid ≤ ready.clock at restFits
    rw [readyClock] at restFits
    omega
  · rw [scopeEq]
    change inner.clock = _
    rw [restClock]
    change ready.clock - restPaid = _
    rw [readyClock]
    omega
  · have lifted := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => Input.LocalEffects.erase {state with memory := inner.memory}) fields
    rw [postMemory, scopeEq]
    exact restFields.trans lifted
  · intro query away
    have different : query ≠ pointer := by simpa using word_away away aligned 0 (by decide) (by decide)
    rw [postMemory, restAway query away]
    change StoreWord.put ready.memory pointer word query = _
    rw [StoreWord.put, if_neg different, memory]

end InitECandidate.Solver.GasBudget.QuadWriter

#print axioms InitECandidate.Solver.GasBudget.QuadWriter.fast_shape
#print axioms InitECandidate.Solver.GasBudget.QuadWriter.fast_normal
