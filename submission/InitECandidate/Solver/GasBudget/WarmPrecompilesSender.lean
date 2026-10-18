import InitECandidate.Solver.GasBudget.WarmPrecompilesConstructorProgram
import InitECandidate.Solver.GasBudget.WarmPrecompilesStep

namespace InitECandidate.Solver.GasBudget.WarmPrecompiles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- The real first sender warm-up establishes population at most one in
the constructor's actual empty table, without a dictionary-success oracle. -/
theorem sender_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (plan : Plan) (sender : BitVec 64)
    (environment : WarmKeys.Environment source) (valid : Valid .account plan) (capacity : plan.capacity = 64)
    (earlier : ∀ pool, plan.base pool + size .account plan pool ≤ cursor) (cursorBound : cursor ≤ 33806089496) (cursorAligned : cursor % 8 = 0)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (header : MemoryModel.Header source.memory .account plan 0#64) (occupied : MemoryModel.Occupied source .account plan [])
    (tableLocal : source.locals.lookup (ofString "aa") = some (.val (.word (cell plan .header 0))))
    (senderLocal : source.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (queryFits : sender.toNat + 20 < 2 ^ 64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress sender offset)))
    (normal : evaluateHOLFiniteState source senderCall = (none, target)) :
    ∃ paid slots, paid ≤ 12 ∧ paid ≤ source.clock ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := source.clock - paid} ∧
      MemoryModel.Header target.memory .account plan (BitVec.ofNat 64 slots.length) ∧ MemoryModel.Occupied target .account plan slots ∧
      target.locals = source.locals ∧ slots.length ≤ 1 ∧ TableFootprint.Frame source.memory target.memory .account plan := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "aa", localVar "sender", .const 1#64] =
      some (TableCall.values (cell plan .header 0) sender 1#64) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, tableLocal, senderLocal, TableCall.values]
  obtain ⟨paid, globals, memory, nextPlan, slots, bounded, unchanged, fits, post, nextValid, nextHalf, sameLocals⟩ :=
    Set.model_call_bound source target .account plan valid cursor cursorBound cursorAligned earlier environment.domain environment.little [] (by simp) header occupied
      sender 1#64 6 capacity (by decide) queryFits queryMapped heap environment.allocCode environment.trapCode environment.zeroCode environment.hashCode environment.copyCode environment.memeqCode
      environment.findCode environment.insertCode environment.growCode environment.setCode _ args normal
  obtain ⟨samePlan, sameGlobals⟩ := post.no_growth valid.positive (by simp only [List.length_nil]; omega)
  subst nextPlan
  subst globals
  have memoryEq := congrArg PanSemStateFiniteExact.memory post.frame
  change target.memory = memory at memoryEq
  have linear := unchanged rfl
  rw [Set.no_growth_caller_price] at linear
  change paid ≤ 12 at linear
  refine ⟨paid, slots, linear, fits, ?_, ?_, post.occupied, sameLocals, post.countBound.2, ?_⟩
  · rw [memoryEq]
    exact post.frame
  · rw [memoryEq]
    exact post.header
  · rw [memoryEq]
    exact post.footprint

end InitECandidate.Solver.GasBudget.WarmPrecompiles

#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.sender_normal
