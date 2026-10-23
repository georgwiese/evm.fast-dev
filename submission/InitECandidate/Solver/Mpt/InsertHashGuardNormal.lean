import InitECandidate.Solver.Mpt.InsertDispatchProgram
import InitECandidate.Solver.Mpt.Fail

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal original insertion hash guard skipped its failing call and
therefore actually observed a non-hash node tag. -/
theorem hash_guard_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source hashGuard=(none,target)) : target=source ∧ tag≠0#64 := by
  by_cases zero : tag=0#64
  · have selected : evaluateHOLFiniteState source hashGuard=evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]):=by
      rw [dispatch_shapes.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact (Fail.call_not_normal source target installed _ (selected.symm.trans normal)).elim
  · have skipped : evaluateHOLFiniteState source hashGuard=(none,source):=by
      rw [dispatch_shapes.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    exact ⟨congrArg Prod.snd (normal.symm.trans skipped),zero⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.hash_guard_normal
