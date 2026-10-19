import InitECandidate.Solver.GasBudget.PreStateReadRecord
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.UnaryCallData

namespace InitECandidate.Solver.GasBudget.PreStateReadRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem call_normal {ι : Type} [DecidableEq ι] (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block query : BitVec 64) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (family : TableFamily.Model source cursor objects) (kind : (objects writer).kind = .account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (blockGlobal : source.globals.lookup (ofString "bs") = some (.val (.word block)))
    (mapped : source.memaddrs (block + 72#64)) (stored : source.memory (block + 72#64) = .word (objects writer).pointer)
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (expressions : List (ExpHOL 64))
    (expectedArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word query)])
    (run : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "record_pre_state_read") expressions) = (none, post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      next.kind = .account ∧ TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      paid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 13 + GrowRuntime.growthPotential .account next.plan.capacity ∧
      (objects writer).slots.length ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length + 1 ∧
      next.plan.capacity ≤ max (objects writer).plan.capacity (4 * (next.slots.length + 1)) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ HeapGlobals source post ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source post := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, callerFields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "record_pre_state_read") expressions run
  obtain ⟨argument, valuesEq, bodyEq, shapeEq, typed, binding⟩ := Input.CallNormal.unary_lookup_data source.code.lookup
    (ofString "record_pre_state_read") (ofString "addr") .one body .one (original_code source.code installed)
    values actual callee shape called
  rw [valuesEq] at args
  have argumentEq : argument = .val (.word query) := by
    have same := Option.some.inj (args.symm.trans expectedArgs)
    simpa using same
  rw [argumentEq] at binding
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  obtain ⟨zero, paid, nextCursor, next, funded, clock, forward, nextKind, nextFamily, pointers, amortized,
    countLower, countUpper, capacity, codes, nextEnvironment, globals, floorFrame⟩ :=
    body_normal entry target block query cursor objects writer entryFamily kind (environment.of_fields rfl rfl rfl)
      blockGlobal mapped stored binding queryFits queryMapped returned bodyRun
  change paid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - paid at clock
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  refine ⟨paid + 1, nextCursor, next, by omega, by rw [postEq]; exact clock.trans subtract, forward, nextKind,
    nextFamily.of_control (by rw [postEq]) (by rw [postEq]) (by rw [postEq]) (by rw [postEq]),
    pointers, by omega, countLower, countUpper, capacity, by rw [postEq]; exact codes,
    nextEnvironment.of_fields (by rw [postEq]) (by rw [postEq]) (by rw [postEq]), ?_, ?_⟩
  · intro key different
    rw [postEq]
    exact globals key different
  · refine ⟨floorFrame.floors, ?_⟩
    intro address before
    rw [postEq]
    exact floorFrame.words address before

end InitECandidate.Solver.GasBudget.PreStateReadRecord

#print axioms InitECandidate.Solver.GasBudget.PreStateReadRecord.call_normal
