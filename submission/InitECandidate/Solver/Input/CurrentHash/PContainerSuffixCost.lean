import InitECandidate.Solver.Input.CurrentHash.PContainerBitLoop
import InitECandidate.Solver.Input.CurrentHash.FixedMemoryCost
import InitECandidate.Solver.Input.CurrentHash.Sha256Pair
import InitECandidate.Solver.Input.CurrentHash.AllocatorCost
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentHash.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_loop_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterLoop 2 := by
  rw [body_shape.2.2.2.2.2.2.2.2.2]
  exact ClockCost.sequence code _ _ 1 1 (Sha256Pair.call_cost code installed (some none) _)
    (ClockCost.sequence code _ _ 1 0 (AllocatorCost.release_call code installed (some none) _) (ClockCost.returned code _))

theorem loop_suffix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat)
    (small : n < 2^63) (installed : OriginalCode.Installed source.code)
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (position : source.locals.lookup (ofString "i") = some (.val (.word 0#64))) :
    source.clock - (evaluateHOLFiniteState source loopAndSuffix).2.clock ≤ n+2 := by
  have loopPrice := bit_loop_cost source n 0 small (by omega) position count
  rw [body_shape.2.2.2.2.2.2.1]
  exact ClockCost.sequence_current source bitLoop afterLoop n 2 (by simpa using loopPrice) (after_loop_cost source.code installed)

theorem after_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat)
    (small : n < 2^63) (installed : OriginalCode.Installed source.code)
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))) :
    source.clock - (evaluateHOLFiniteState source afterZero).2.clock ≤ n+2 := by
  let entry := bind source "i" 0#64
  have next : entry.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))) :=
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans count
  have price := loop_suffix_cost entry n small installed next (bind_lookup_same _ _ _)
  rw [body_shape.2.2.2.2.2.1]
  exact ClockCost.declared_current source "i" (.const 0#64) 0#64 loopAndSuffix (n+2) rfl price

theorem after_act_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat)
    (small : n < 2^63) (installed : OriginalCode.Installed source.code)
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))) :
    source.clock - (evaluateHOLFiniteState source afterAct).2.clock ≤ n+44 := by
  rw [body_shape.2.2.2.2.1]
  have paid := ClockCost.sequence_reached_current source _ afterZero 42 (n+2)
    (FixedMemoryCost.zero source.code installed (some none) (localVar "act") 32 (by decide) source rfl) (by
      intro middle normal
      have nextCount := (CallNormal.ignored_lookup source middle (ofString "n") (ofString "memzero") zeroArguments normal).trans count
      have nextCode : OriginalCode.Installed middle.code := by
        rw [(evaluation_fields source middle _ none normal).2.2.2]
        exact installed
      exact after_zero_cost middle n small nextCode nextCount)
  exact Nat.le_trans paid (by omega)

/-- Actual activity allocation suffix, with arbitrary temporary/output pointers
and every source outcome. Only the real field count affects its runtime. -/
theorem after_progressive_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tmp : BitVec 64) (n : Nat)
    (small : n < 2^63) (installed : OriginalCode.Installed source.code)
    (temporary : source.locals.lookup (ofString "tmp") = some (.val (.word tmp)))
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))) :
    source.clock - (evaluateHOLFiniteState source afterProgressive).2.clock ≤ n+44 := by
  let act := tmp+32#64
  let entry := bind source "act" act
  have nextCount : entry.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))) :=
    (bind_lookup_other source "act" "n" act (by decide)).trans count
  have price := after_act_cost entry n small installed nextCount
  have read : eval source (.op .add [localVar "tmp", .const 32#64]) = some (.val (.word act)) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, temporary, valueIsWord, valueWord, wordOpHOL, wordOp, act]
  rw [body_shape.2.2.2.1]
  exact ClockCost.declared_current source "act" _ act afterAct (n+44) read price

end InitECandidate.Solver.Input.CurrentHash.PContainer

#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_loop_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.loop_suffix_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_zero_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_act_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_progressive_cost
