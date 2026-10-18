import InitECandidate.Solver.GasBudget.StateFreshTxOwned
import InitECandidate.Solver.Input.IgnoredCallNormal
import InitECandidate.Solver.GasBudget.JournalCounterLedger

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem result_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (bs : BitVec 64) :
    (resultState source start bs).code = source.code := by
  calc
    _ = (blockStateStored source start bs).code := scoped_code first rest (blockStateStored source start bs) (start + 72) start
    _ = source.code := rfl

/-- The actual ignored-result original caller adds one clock to the entire
81-clock body and restores all caller locals. Its post-state owns all old
tables, all eight new tables and the journal reservation. -/
theorem call_normal {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start : Nat) (objects : ι → TableFamily.Object) (base cap : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source start objects) (zone : Journal.Zone objects base cap start)
    (environment : WarmKeys.Environment source) (lower : 2701131776 ≤ start)
    (bounded : start ≤ 33806089496) (aligned : start % 8 = 0) (oldTs bs : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (ts : source.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (blockState : source.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (code : source.code.lookup (ofString "state_fresh_tx") = some ([], body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "state_fresh_tx") []) = (none, target)) :
    82 ≤ source.clock ∧ target.clock = source.clock - 82 ∧ start + 17176 ≤ 33806089496 ∧
      TableFamily.Model target (start + 17176) (objectsAfter objects (start + 72) (first :: rest)) ∧
      Journal.Zone (objectsAfter objects (start + 72) (first :: rest)) base cap (start + 17176) ∧
      Journal.Image target (objectsAfter objects (start + 72) (first :: rest)) base 0 (fun index => promoteEntry 8 (entries index)) ∧
      Fields target start (objectsAfter objects (start + 72) (first :: rest)) (first :: rest) ∧
      target.memory (MemoryRegion.address ⟨start, 72⟩ 0) = .word bs ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) ∧
      target.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 start))) ∧
      target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 17176)))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧
      Journal.CounterEffect source target 0 0 (Journal.currentCount source) := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "state_fresh_tx") [] = some (body, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup source.code.lookup (ofString "state_fresh_tx") [] body (fun _ => none) .one raw
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "state_fresh_tx") [] [] body callee .one rfl called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry start objects := family.of_control rfl rfl rfl rfl
  obtain ⟨returnedEq, funded, clockEq, postEq, room, models, nextZone, nextImage, fields, savedBs, counter, finalTs, finalHeap, nextEnvironment⟩ :=
    owned_normal entry post start objects base cap entries entryFamily zone (environment.of_fields rfl rfl rfl) lower bounded aligned oldTs bs
      heap ts blockState newCode returned bodyRun
  rw [returnedEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "state_fresh_tx") [] [] body callee .one
    (.val (.word 0#64)) post rfl called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have targetEq := congrArg Prod.snd (normal.symm.trans actual)
  change target = {post with locals := source.locals} at targetEq
  subst target
  have codes : post.code = source.code := by rw [postEq]; exact result_code entry start bs
  change 81 ≤ source.clock - 1 at funded
  change post.clock = source.clock - 1 - 81 at clockEq
  exact ⟨by omega, by change post.clock = _; omega, room, models.of_control rfl rfl rfl rfl, nextZone,
    Journal.Image.empty _ _ _ _, fields, savedBs, counter, finalTs, finalHeap, rfl, codes, nextEnvironment.of_fields rfl rfl rfl,
    Journal.CounterEffect.reset source _ counter⟩

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.result_code
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.call_normal
