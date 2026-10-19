import InitECandidate.Solver.GasBudget.MemoryWriterPrice
import InitECandidate.Solver.Input.PricedScalarPrefix
import InitECandidate.Solver.Input.KnownUnaryPrefix
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.GasBudget.MemoryWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

set_option maxHeartbeats 1000000 in
theorem be64_fast_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer))) (mapped : source.memaddrs pointer)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source (fast .be64) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ 1 ≤ source.clock ∧ post.clock = source.clock - 1 ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} ∧
      ∃ word : BitVec 64, post.memory = StoreWord.put source.memory pointer word := by
  simp only [fast, Kind.body, Kind.signature, Kind.original, Guest.guestFn_st_be64, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none] at normal
  let finish : ProgHOL 64 := .seq (.store (localVar "p") (localVar "w")) (.return (.const 0#64))
  have env := OriginalCodeEnvironment.arithmetic source.code installed
  obtain ⟨paid, word, ready, inner, positive, bound, fits, readyEq, fields, run, scopeEq⟩ :=
    Input.PricedScalarPrefix.normal source post "w" (ofString "bswap64") [localVar "v"] finish
      ArithmeticEffects.Kind.bswap64.signature.1 ArithmeticEffects.Kind.bswap64.body ArithmeticEffects.Kind.bswap64.signature.2.2 0
      (env .bswap64) (ArithmeticEffects.pure_bswap64 source.code env)
      (Input.ClockCost.of_quiet source.code _ (ArithmeticEffects.quiet_preserves .bswap64 source.code (by rfl))) returned normal
  have paidEq : paid = 1 := by omega
  subst paid
  have readyP := (Input.KnownUnaryPrefix.lookup_other readyEq "p" (by decide)).trans pointerLocal
  have readyW := Input.KnownUnaryPrefix.lookup_same readyEq
  have readyMapped : ready.memaddrs pointer := by rw [readyEq]; exact mapped
  have storeRun := StoreWord.execute ready (localVar "p") (localVar "w") pointer word
    (by simp [eval, evalHOLExact, toExact, localVar, readyP]) (by simp [eval, evalHOLExact, toExact, localVar, readyW]) readyMapped
  let stored := {ready with memory := StoreWord.put ready.memory pointer word}
  change evaluateHOLFiniteState ready (.seq (.store (localVar "p") (localVar "w")) (.return (.const 0#64))) = _ at run
  rw [StateSteps.next_sequence ready stored _ _ storeRun (Nat.le_refl _)] at run
  obtain ⟨read, finalEq⟩ := Input.return_normal stored inner (.const 0#64) returned run
  have value : returned = .val (.word 0#64) := (Option.some.inj read).symm
  have memory := Input.LocalEffects.memory_of_erase source ready fields
  have postMemory : post.memory = StoreWord.put source.memory pointer word := by
    rw [scopeEq, finalEq]
    change StoreWord.put ready.memory pointer word = _
    rw [memory]
  have postFields : Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} := by
    rw [postMemory]
    have relation := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
      Input.LocalEffects.erase {state with memory := StoreWord.put state.memory pointer word}) fields
    rw [scopeEq, finalEq]
    exact relation
  refine ⟨value, fits, ?_, postFields, word, postMemory⟩
  rw [scopeEq, finalEq]
  change ready.clock = source.clock - 1
  rw [readyEq]
  rfl

end InitECandidate.Solver.GasBudget.MemoryWriter

#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be64_fast_normal
