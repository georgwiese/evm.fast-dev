import InitECandidate.Solver.Mpt.CurrentWitnessCoreDecode
import InitECandidate.Solver.Mpt.WitnessCoreLoopControl
import InitECandidate.Solver.Input.ClockCostPotentialLoop

namespace InitECandidate.Solver.Mpt.WitnessCore
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

structure CurrentDecodeEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState source
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  dbCell : source.locals.lookup (ofString "db")=some (.val (.word db))
  pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer))
  lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length))
  resultCell : source.locals.lookup (ofString "result")=some (.val (.word 0#64))
  modeCell : source.locals.lookup (ofString "mode")=some (.val (.word 1#64))
  topCell : source.locals.lookup (ofString "top")=some (.val (.word 0#64))
  goCell : source.locals.lookup (ofString "go")=some (.val (.word 1#64))

structure CurrentFinishEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (go : BitVec 64) : Prop where
  modeCell : source.locals.lookup (ofString "mode")=some (.val (.word 0#64))
  topCell : source.locals.lookup (ofString "top")=some (.val (.word 0#64))
  goCell : source.locals.lookup (ofString "go")=some (.val (.word go))

theorem current_finish_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (go : BitVec 64) (entry : CurrentFinishEntry source go) :
    evaluateHOLFiniteState source loopBody=(none,bind source "go" 0#64) := by
  have choice : evaluateHOLFiniteState source returnBranch=evaluateHOLFiniteState source finishReturn := by
    rw [return_shape]
    simp [evaluateHOLFiniteState_ite,evalHOLExact,localVar,entry.topCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [loop_body_choice source 0#64 entry.modeCell]
  simp only [show (0#64 : BitVec 64)≠1#64 from by decide,show (0#64 : BitVec 64)≠2#64 from by decide,if_false]
  rw [choice,finish_return_shape]
  exact StateSteps.assign_execute source "go" (.const 0#64) go 0#64 entry.goCell rfl

noncomputable def currentAllowance (length : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat := by
  classical
  exact if source.locals.lookup (ofString "mode")=some (.val (.word 1#64)) then length.toNat/4+195*length.toNat+287
    else if source.locals.lookup (ofString "go")=some (.val (.word 0#64)) then 0 else 1

theorem current_allowance_decode (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (cell : source.locals.lookup (ofString "mode")=some (.val (.word 1#64))) :
    currentAllowance length source=length.toNat/4+195*length.toNat+287 := by simp [currentAllowance,cell]

theorem current_allowance_finish (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length go : BitVec 64)
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word 0#64)))
    (goCell : source.locals.lookup (ofString "go")=some (.val (.word go))) :
    currentAllowance length source=if go=0#64 then 0 else 1 := by simp [currentAllowance,modeCell,goCell]

/-- Only the actual first decode and empty-stack return iteration are
reachable. Each pays its own price; the expensive decode price is not charged
again for the one-tick exit iteration. All stopped outcomes are included. -/
theorem current_loop_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64) (entry : CurrentDecodeEntry source db pointer length heap)
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source (.while condition loopBody)).2.clock≤length.toNat/4+195*length.toNat+287 := by
  let invariant:=fun current=>CurrentDecodeEntry current db pointer length heap ∨ ∃ go,CurrentFinishEntry current go
  have step (current : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : current.code=source.code)
      (valid : invariant current) (word : BitVec 64)
      (guard : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) condition=some (.val (.word word)))
      (nonzero : word≠0) (funded : current.clock≠0) :
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
      current.clock-output.2.clock≤currentAllowance length current ∧
      ((output.1=none ∨ output.1=some .continue)→invariant output.2 ∧
        current.clock-output.2.clock+currentAllowance length output.2≤currentAllowance length current) := by
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
    rcases valid with first|⟨go,last⟩
    · have currentPrice:=current_allowance_decode current length first.modeCell
      have chosen:=loop_body_choice (decClockHOLFinite current) 1#64 first.modeCell
      rw [if_pos rfl] at chosen
      have price:=current_decode_branch_price (decClockHOLFinite current) db pointer length heap first.dbCell first.pointerCell first.lengthCell
        small before first.heapCell heapArena heapBound aligned (first.arena.of_frame rfl)
      rw [←chosen] at price
      change current.clock-1-output.2.clock≤length.toNat/4+195*length.toNat+285 at price
      have paid : current.clock-output.2.clock≤length.toNat/4+195*length.toNat+286:=by omega
      refine ⟨Nat.le_trans paid (by rw [currentPrice]; omega),?_⟩
      intro continuing
      have normal : output.1=none:=continuing.resolve_right (loop_body_no_continue (decClockHOLFinite current))
      have run : evaluateHOLFiniteState (decClockHOLFinite current) decodeBranch=(none,output.2):=by rw [←chosen]; exact Prod.ext normal rfl
      obtain ⟨modeCell,topCell,goCell⟩:=current_decode_branch_none (decClockHOLFinite current) output.2 db pointer length heap 0#64 1#64
        first.dbCell first.pointerCell first.lengthCell first.resultCell first.modeCell first.topCell first.goCell small before
        first.heapCell heapArena heapBound aligned (first.arena.of_frame rfl) run
      have next : CurrentFinishEntry output.2 1#64:=⟨modeCell,topCell,goCell⟩
      have nextPrice:=current_allowance_finish output.2 length 1#64 modeCell goCell
      simp only [show (1#64 : BitVec 64)≠0#64 from by decide,if_false] at nextPrice
      exact ⟨Or.inr ⟨1#64,next⟩,by rw [currentPrice,nextPrice]; exact Nat.add_le_add_right paid 1⟩
    · have read : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) condition=
          some (.val (.word (if go=0#64 then 0#64 else 1#64))) := by
        simp [condition,evalHOLFinite,evalHOLExact,localVar,toExact,last.goCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      have same : word=(if go=0#64 then 0#64 else 1#64):=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (guard.symm.trans read)))
      have running : go≠0#64:=by intro zero; rw [zero,if_pos rfl] at same; exact nonzero same
      have currentPrice:=current_allowance_finish current length go last.modeCell last.goCell
      rw [if_neg running] at currentPrice
      have after : evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,bind (decClockHOLFinite current) "go" 0#64):=
        current_finish_execute (decClockHOLFinite current) go ⟨last.modeCell,last.topCell,last.goCell⟩
      change current.clock-(evaluateHOLFiniteState (decClockHOLFinite current) loopBody).2.clock≤_ ∧ _
      rw [after]
      have next : CurrentFinishEntry (bind (decClockHOLFinite current) "go" 0#64) 0#64:=
        ⟨(bind_lookup_other _ "go" "mode" 0#64 (by decide)).trans last.modeCell,
          (bind_lookup_other _ "go" "top" 0#64 (by decide)).trans last.topCell,bind_lookup_same _ _ _⟩
      have nextPrice:=current_allowance_finish _ length 0#64 next.modeCell next.goCell
      simp at nextPrice
      refine ⟨?_,fun _=>⟨Or.inr ⟨0#64,next⟩,?_⟩⟩
      · change current.clock-(current.clock-1)≤currentAllowance length current
        rw [currentPrice]; omega
      · change current.clock-(current.clock-1)+currentAllowance length _≤currentAllowance length current
        rw [currentPrice,nextPrice]; omega
  have result:=ClockCost.potential_loop source.code condition loopBody invariant (currentAllowance length) step source rfl (Or.inl entry)
  rw [current_allowance_decode source length entry.modeCell] at result
  exact result

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_finish_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_loop_price
