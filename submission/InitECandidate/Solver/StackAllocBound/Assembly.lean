import InitECandidate.Solver.StackAllocBound.Calls
import InitECandidate.Solver.StackAllocBound.StoreConsts

/-! The eligible allocation-lowering pass uses zero extra clock. Actual source
runs, original compiler premises and every original postcondition are retained. -/
namespace InitECandidate.Solver.StackAllocBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

theorem goal_all {width : Nat} [NeZero width] {C F : Type} (anything : WordSemGcFun width)
    (cr : CompileFn width C) :
    ∀ (mm : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = mm → eligible p = true → StateSafe s → ZeroGoal anything cr p s := by
  intro mm
  induction mm using EvaluateAddClock.lexNat_wf.induction with
  | _ mm ih =>
  intro p s hm safe stateSafe
  subst hm
  have ihp : ZeroIH anything cr p s := fun q u hlt => ih _ hlt q u rfl
  cases p with
  | skip => exact goal_skip anything cr s
  | halt v => exact goal_halt anything cr s v
  | tick => exact goal_tick anything cr s
  | ret v => exact goal_ret anything cr s v
  | raise v => exact goal_raise anything cr s v
  | «break» v => exact goal_break anything cr s v
  | «continue» v => exact goal_continue anything cr s v
  | inst i => exact goal_inst anything cr s i
  | get v name => exact goal_get anything cr s v name
  | set name v => exact goal_set anything cr s name v
  | opCurrHeap b v src => exact goal_opCurrHeap anything cr s b v src
  | alloc k => simp only [eligible, Bool.false_eq_true] at safe
  | storeConsts t1 t2 stub =>
    cases stub with
    | none => exact goal_storeConsts_none anything cr s t1 t2
    | some loc => simp only [eligible, Bool.false_eq_true] at safe
  | seq c1 c2 => exact goal_seq anything cr s c1 c2 safe stateSafe ihp
  | ite cmp r1 ri c1 c2 => exact goal_ite anything cr s cmp r1 ri c1 c2 safe stateSafe ihp
  | loop c1 => exact goal_loop anything cr s c1 safe stateSafe ihp
  | jumpLower r1 r2 dest => exact goal_jumpLower anything cr s r1 r2 dest safe stateSafe ihp
  | rawCall dest => exact goal_rawCall anything cr s dest safe stateSafe ihp
  | call ret dest handler =>
      rcases ret with _ | ⟨retH, link, l1, l2⟩
      · exact goal_call_none anything cr s dest handler safe stateSafe ihp
      · exact goal_call_some anything cr s retH link l1 l2 dest handler safe stateSafe ihp
  | install a b c d e => simp only [eligible, Bool.false_eq_true] at safe
  | shMemOp op v addr => exact goal_shMemOp anything cr s op v addr
  | codeBufferWrite a b => exact goal_codeBufferWrite anything cr s a b
  | dataBufferWrite a b => exact goal_dataBufferWrite anything cr s a b
  | ffi fi p1 p2 p3 p4 p5 => exact goal_ffi anything cr s fi p1 p2 p3 p4 p5
  | locValue v l1 l2 => exact goal_locValue anything cr s v l1 l2
  | stackAlloc k => exact goal_stackAlloc anything cr s k
  | stackFree k => exact goal_stackFree anything cr s k
  | stackLoad a k => exact goal_stackLoad anything cr s a k
  | stackLoadAny a rn => exact goal_stackLoadAny anything cr s a rn
  | stackStore a k => exact goal_stackStore anything cr s a k
  | stackStoreAny a rn => exact goal_stackStoreAny anything cr s a rn
  | stackGetSize a => exact goal_stackGetSize anything cr s a
  | stackSetSize a => exact goal_stackSetSize anything cr s a
  | bitmapLoad a v => exact goal_bitmapLoad anything cr s a v

theorem zeroCompCorrect {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (safe : eligible p = true) (stateSafe : StateSafe s)
    (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (m n : Nat) (c : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW width))
    (run : evaluate (p, s) = (r, t)) (nonError : r ≠ some .error)
    (arguments : allocArg p) (pre : Pre cr c s regs) :
    ∃ regs1, evaluate ((comp n m p).1, Tgt anything cr c s 0 regs) =
      (r, Res anything cr c t regs1) ∧ Post r t regs1 := by
  obtain ⟨ck, regs1, zero, run, post⟩ :=
    goal_all anything cr _ p s rfl safe stateSafe r t m n c regs run nonError arguments pre
  subst ck
  exact ⟨regs1, run, post⟩

end InitECandidate.Solver.StackAllocBound
#print axioms InitECandidate.Solver.StackAllocBound.goal_all
#print axioms InitECandidate.Solver.StackAllocBound.zeroCompCorrect
