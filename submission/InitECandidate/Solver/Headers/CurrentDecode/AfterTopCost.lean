import InitECandidate.Solver.Headers.CurrentDecode.AfterKindCost
import InitECandidate.Solver.Input.ClockCostGuardReached

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

/-- The actual list-kind guard either stops without a source tick or
supplies its true kind to the complete current slicing/field suffix. -/
theorem after_top_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag heap : BitVec 64)
    (topCell : source.locals.lookup (ofString "top")=some (Rlp.Item.result pointer header payload flag))
    (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : (pointer+header).toNat+payload.toNat≤heap.toNat) :
    source.clock-(evaluateHOLFiniteState source afterTop).2.clock≤149*payload.toNat+460 := by
  have read : eval source (.cmp .notEqual (.rfield 0 (localVar "top")) (.const 1#64))=some (.val (.word (if flag≠1#64 then 1#64 else 0#64))) := by
    simp [eval,evalHOLExact,localVar,toExact,topCell,Rlp.Item.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [after_top_shape.1]
  unfold kindGuard
  have actual:=ClockCost.stopping_guard_reached source (.cmp .notEqual (.rfield 0 (localVar "top")) (.const 1#64))
    (.raise (ofString "HdrErr") (.const 10#64)) afterKind 0 (149*payload.toNat+460)
    (raise_ne_none source _ _) (ClockCost.raised source.code _ _ source rfl) ?_
  · exact Nat.le_trans actual (Nat.le_of_eq (Nat.zero_max _))
  · intro passed
    have one : flag=1#64 := by
      apply Classical.byContradiction
      intro different
      have chosen : evaluateHOLFiniteState source (.ite (.cmp .notEqual (.rfield 0 (localVar "top")) (.const 1#64)) (.raise (ofString "HdrErr") (.const 10#64)) .skip)=evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 10#64)) := by
        change @evalHOLExact 64 Guest.HostMemory _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query)) _=_ at read
        rw [evaluateHOLFiniteState_ite,read,if_pos different]
        simp
      rw [chosen] at passed
      exact raise_ne_none source (ofString "HdrErr") (.const 10#64) (congrArg Prod.fst passed)
    subst flag
    exact after_kind_cost source pointer header payload heap topCell arena heapGlobal heapBound heapLower heapAligned before

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.after_top_cost
