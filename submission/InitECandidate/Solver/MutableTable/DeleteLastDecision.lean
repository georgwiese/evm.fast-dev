import InitECandidate.Solver.MutableTable.DeleteLastSwap

namespace InitECandidate.Solver.MutableTable.Delete.Finish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original final comparison and optional last-entry swap. The last
slot is read and required in range only on the branch that actually swaps. -/
theorem last_swap_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : Nat) (deleted : Fin count) (entries : Fin count → Nat)
    (room : count < plan.capacity) (locals : SwapLocals source plan deleted.val (count - 1))
    (slotInside : deleted.val ≠ count - 1 → entries (lastOrdinal deleted) < plan.capacity)
    (readLast : deleted.val ≠ count - 1 → source.memory (cell plan .order (8 * (count - 1))) = .word (BitVec.ofNat 64 (entries (lastOrdinal deleted)))) :
    evaluateHOLFiniteState source (.ite Delete.lastTest Delete.lastBranch .skip) =
      (none, {source with memory := swapMemory source.memory plan deleted entries}) := by
  classical
  have countPositive : 0 < count := by have := deleted.isLt; omega
  have ordinalInside : deleted.val < plan.capacity := Nat.lt_trans deleted.isLt room
  have lastInside : count - 1 < plan.capacity := by omega
  by_cases last : deleted.val = count - 1
  · have sameWord : BitVec.ofNat 64 deleted.val = BitVec.ofNat 64 (count - 1) := congrArg (BitVec.ofNat 64) last
    simp [evaluateHOLFiniteState_ite, Delete.lastTest, localVar, evalHOLExact, toExact, locals.deleted, locals.last,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, sameWord, swapMemory, last]
  · have different : BitVec.ofNat 64 deleted.val ≠ BitVec.ofNat 64 (count - 1) := by
      intro same
      have numeric := congrArg BitVec.toNat same
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans ordinalInside (capacity_small kind plan valid)),
        Nat.mod_eq_of_lt (Nat.lt_trans lastInside (capacity_small kind plan valid))] at numeric
      exact last numeric
    have branchRun := last_branch_execute source kind plan valid domain deleted.val (count - 1) (entries (lastOrdinal deleted)) ordinalInside lastInside (slotInside last) locals (readLast last)
    simp [evaluateHOLFiniteState_ite, Delete.lastTest, localVar, evalHOLExact, toExact, locals.deleted, locals.last,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, different, branchRun, swapMemory, last]

end InitECandidate.Solver.MutableTable.Delete.Finish

#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.last_swap_execute
