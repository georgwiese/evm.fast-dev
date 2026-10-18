import InitECandidate.Solver.GasBudget.StackPopCallException
import InitECandidate.Solver.GasBudget.StackPopsPrefix

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Actual prefix effects before the first charge: only sp may change,
and source call clocks are paid exactly. Locals are lexical bookkeeping. -/
structure PrefixEffect (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (paid : Nat) : Prop where
  fits : paid ≤ source.clock
  clock : target.clock = source.clock - paid
  fields : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := target.clock}
  budget : regularBudget target.memory frame = regularBudget source.memory frame
  used : target.memory (frame + 184#64) = source.memory (frame + 184#64)
  outside : ∀ address, address ≠ frame + 16#64 → target.memory address = source.memory address

theorem PrefixEffect.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) :
    PrefixEffect source source frame 0 := by
  exact ⟨Nat.zero_le _, by simp, rfl, rfl, rfl, by intros; rfl⟩

theorem PrefixEffect.resumed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (name : String) (returned : ValueHOL 64) (positive : 1 ≤ source.clock) :
    PrefixEffect source (resumed source frame sp name returned) frame 1 := by
  refine ⟨positive, rfl, rfl, ?_, ?_, ?_⟩
  · exact FrameField.put_budget source.memory frame 16#64 (sp - 1#64) (by decide) (by decide) (by decide)
  · exact FrameField.put_other source.memory frame 16#64 (sp - 1#64) 184#64 (by decide)
  · intro address away
    exact if_neg away

theorem PrefixEffect.unchanged (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (paid : Nat)
    (fits : paid ≤ source.clock) (clock : target.clock = source.clock - paid)
    (fields : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid}) :
    PrefixEffect source target frame paid := by
  have memory := congrArg PanSemStateFiniteExact.memory fields
  change target.memory = source.memory at memory
  refine ⟨fits, clock, ?_, ?_, ?_, ?_⟩
  · rw [memory, clock]
    exact fields
  · rw [memory]
  · exact congrFun memory _
  · intro address _
    exact congrFun memory address

theorem PrefixEffect.restore {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : PrefixEffect source target frame paid) (saved : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) :
    PrefixEffect source (restore saved name target) frame paid :=
  ⟨effect.fits, effect.clock, effect.fields, effect.budget, effect.used, effect.outside⟩

theorem PrefixEffect.of_emptyLocals {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : PrefixEffect source middle frame paid)
    (same : emptyLocalsHOLFinite target = emptyLocalsHOLFinite middle) : PrefixEffect source target frame paid := by
  have memory := congrArg PanSemStateFiniteExact.memory same
  change target.memory = middle.memory at memory
  have clock := congrArg PanSemStateFiniteExact.clock same
  change target.clock = middle.clock at clock
  refine ⟨effect.fits, clock.trans effect.clock, ?_, ?_, ?_, ?_⟩
  · rw [same, effect.fields, memory, clock]
  · rw [memory]
    exact effect.budget
  · rw [memory]
    exact effect.used
  · intro address away
    rw [memory]
    exact effect.outside address away

theorem PrefixEffect.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {first second : Nat}
    (left : PrefixEffect source middle frame first) (right : PrefixEffect middle target frame second) :
    PrefixEffect source target frame (first + second) := by
  have frameLift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := target.memory, clock := target.clock}) left.fields
  refine ⟨?_, ?_, right.fields.trans frameLift, right.budget.trans left.budget, right.used.trans left.used, ?_⟩
  · have a := left.fits
    have b := right.fits
    rw [left.clock] at b
    omega
  · rw [right.clock, left.clock]
    omega
  · intro address away
    exact (right.outside address away).trans (left.outside address away)

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.refl
#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.resumed
#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.unchanged
#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.restore
#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.of_emptyLocals
#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.trans
