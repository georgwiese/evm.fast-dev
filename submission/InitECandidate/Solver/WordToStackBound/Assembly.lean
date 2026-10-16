import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import InitECandidate.Solver.WordToStackBound.Alloc
import InitECandidate.Solver.WordToStackBound.Call
import InitECandidate.Solver.WordToStackBound.Clock
import InitECandidate.Solver.WordToStackBound.CodeBufferWrite
import InitECandidate.Solver.WordToStackBound.Control
import InitECandidate.Solver.WordToStackBound.DataBufferWrite
import InitECandidate.Solver.WordToStackBound.FFI
import InitECandidate.Solver.WordToStackBound.Flat
import InitECandidate.Solver.WordToStackBound.Get
import InitECandidate.Solver.WordToStackBound.If
import InitECandidate.Solver.WordToStackBound.Inst
import InitECandidate.Solver.WordToStackBound.LocValue
import InitECandidate.Solver.WordToStackBound.Loop
import InitECandidate.Solver.WordToStackBound.MoveFull
import InitECandidate.Solver.WordToStackBound.OpCurrHeap
import InitECandidate.Solver.WordToStackBound.Raise
import InitECandidate.Solver.WordToStackBound.Return
import InitECandidate.Solver.WordToStackBound.Seq
import InitECandidate.Solver.WordToStackBound.Set
import InitECandidate.Solver.WordToStackBound.ShareInst
import InitECandidate.Solver.WordToStackBound.StoreConsts

namespace InitECandidate.Solver.WordToStackBound
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang

/-- Bounded simulation for the full Word evaluator, retaining the compiler's
state relation, resource outcomes, and all original compilation guards. -/
theorem compCorrect {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) :
    ∀ (program : WordLangProgHOL (BitVec width))
      (source : WordSemStateFiniteExact width (Nat × C) F),
      Simulation ac limit program source := by
  apply WordSemStateFiniteExact.evaluate_ind (fun p s => Simulation ac limit p s)
  refine ⟨?skip, ?alloc, ?storeConsts, ?move, ?inst, ?assign, ?get, ?set, ?opCurrHeap, ?store,
    ?tick, ?mustTerminate, ?seq, ?ret, ?raise, ?brk, ?cont, ?ite, ?loop, ?locValue, ?install,
    ?codeBufferWrite, ?dataBufferWrite, ?ffi, ?shareInst, ?call⟩
  case skip => exact fun s => Control.compCorrectSkip ac limit s
  case alloc => exact fun n names s => Alloc.compCorrectAlloc ac limit n names s
  case storeConsts => exact fun t1 t2 a o w s => StoreConsts.compCorrectStoreConsts (limit := limit) ac t1 t2 a o w s
  case move => exact fun pri moves s => MoveFull.compCorrectMove ac limit pri moves s
  case inst => exact fun i s => Inst.compCorrectInst ac limit i s
  case assign => exact fun v e s => Flat.compCorrectAssign ac limit v e s
  case get => exact fun v name s => Get.compCorrectGet ac limit v name s
  case set => exact fun v e s => Set.compCorrectSet ac limit v e s
  case opCurrHeap => exact fun b d src s => OpCurrHeap.compCorrectOpCurrHeap ac limit b d src s
  case store => exact fun e v s => Flat.compCorrectStore ac limit e v s
  case tick => exact fun s => Clock.compCorrectTick ac limit s
  case mustTerminate => exact fun p s _ => Clock.compCorrectMustTerminate ac limit p s
  case seq => exact fun c1 c2 s ih => Seq.compCorrectSeq ac limit c1 c2 s ih
  case ret => exact fun n ms s => Return.compCorrectReturn ac limit n ms s
  case raise => exact fun n s => Raise.compCorrectRaise ac limit n s
  case brk => exact fun l s => Control.compCorrectBreak ac limit l s
  case cont => exact fun l s => Control.compCorrectContinue ac limit l s
  case ite => exact fun cmp r ri c1 c2 s ih => If.compCorrectIf ac limit cmp r ri c1 c2 s ih
  case loop => exact fun names c exitNames s ih => Loop.compCorrectLoop ac limit names exitNames c s ih
  case locValue => exact fun r l s => LocValue.compCorrectLocValue ac limit r l s
  case install => exact fun p l dp dl names s => Flat.compCorrectInstall ac limit p l dp dl names s
  case codeBufferWrite => exact fun r1 r2 s => CodeBufferWrite.compCorrectCodeBufferWrite ac limit r1 r2 s
  case dataBufferWrite => exact fun r1 r2 s => DataBufferWrite.compCorrectDataBufferWrite ac limit r1 r2 s
  case ffi => exact fun i p1 l1 p2 l2 names s => FFI.compCorrectFFI ac limit i p1 l1 p2 l2 names s
  case shareInst => exact fun op v e s => ShareInst.compCorrectShareInst ac limit op v e s
  case call => exact fun ret dest args handler s ih => Call.compCorrectCall ac limit ret dest args handler s ih

#print axioms InitECandidate.Solver.WordToStackBound.compCorrect
end InitECandidate.Solver.WordToStackBound
