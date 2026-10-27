import InitECandidate.Solver.Input.CurrentStartup.PayloadEntry
import InitECandidate.Solver.Input.PayloadPrefixProgram

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadCut
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def actions : List CallPrefix.Action :=
  [.scoped (ofString "pl") .one (Code.name .alloc) [.const 136#64],
   .command Payload.pointerStore, .command Payload.lengthStore,
   .declare (ofString "o_extra") .one (Scalar.flat32 (WitnessRadix.QueryBranch.localVar "p") [436]),
   .declare (ofString "o_txs") .one (Scalar.flat32 (WitnessRadix.QueryBranch.localVar "p") [504]),
   .declare (ofString "o_wd") .one (Scalar.flat32 (WitnessRadix.QueryBranch.localVar "p") [508]),
   .declare (ofString "o_bal") .one (Scalar.flat32 (WitnessRadix.QueryBranch.localVar "p") [528])]

theorem source_shape : Payload.afterGuard = CallPrefix.program actions Payload.offsetBody := by
  simpa only [Payload.prefixActions, WitnessRadix.ProgramPrefix.program, actions, CallPrefix.program, Code.name] using Payload.prefix_shape

theorem actions_safe : actions.all (fun action => action.keeps (ofString "unused")) = true := by decide

theorem kept_pl : (actions.drop 1).all (fun action => action.keeps (ofString "pl")) = true := by decide

theorem actions_heap (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Preserves code (CallPrefix.program actions .skip) := by
  simp only [actions, CallPrefix.program]
  refine NormalHeapEffects.scoped_body code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (HeapMonotone.alloc code installed) ?_
  refine NormalHeapEffects.sequence code _ _ (NormalHeapEffects.store code _ _) ?_
  refine NormalHeapEffects.sequence code _ _ (NormalHeapEffects.store code _ _) ?_
  exact NormalHeapEffects.declared code _ _ _ _ (NormalHeapEffects.declared code _ _ _ _
    (NormalHeapEffects.declared code _ _ _ _ (NormalHeapEffects.declared code _ _ _ _ (NormalHeapEffects.skip code))))

/-- Actual payload return reaches all seven literal header actions without
requiring future room, successful stores/reads or a minimum source clock. -/
theorem reached (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower : Nat)
    (installed : OriginalCode.Installed source.code) (heap : NormalHeapEffects.AtLeast lower source)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source Payload.afterGuard = (some (.returned value), post)) :
    ∃ current inner, CallPrefix.Execution source actions current ∧ NormalHeapEffects.AtLeast lower current ∧
      evaluateHOLFiniteState current Payload.offsetBody = (some (.returned value), inner) ∧
      post.clock = inner.clock ∧ LocalEffects.erase post = LocalEffects.erase inner := by
  rw [source_shape] at actual
  have never : NoReturn.Never (CallPrefix.program actions .skip) := @CallPrefix.kept_never actions (ofString "unused") (by
    intro action member
    exact List.all_eq_true.mp actions_safe action member)
  obtain ⟨current, inner, execution, remaining, clock, frame⟩ := CallPrefix.normal_frame_trace source post actions Payload.offsetBody value never actual
  exact ⟨current, inner, execution, NormalHeapEffects.execution execution (actions_heap source.code installed) lower heap, remaining, clock, frame⟩

/-- The real136-byte payload allocation returns the incoming frontier as
pl, and actual return derives the entire allocation's room. -/
theorem record_pointer {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (lower : Nat)
    (installed : OriginalCode.Installed source.code) (heap : NormalHeapEffects.AtLeast lower source)
    (actual : CallPrefix.Execution source actions target) :
    ∃ pointer : BitVec 64, lower ≤ pointer.toNat ∧ pointer.toNat % 8 = 0 ∧
      pointer.toNat + 136 ≤ 2952790016 ∧ target.locals.lookup (ofString "pl") = some (.val (.word pointer)) := by
  cases actual with
  | @step _ allocatedState _ _ _ allocated rest =>
    obtain ⟨pointer, heapCell, low, aligned, room, stateEq⟩ := allocation_frontier (ofString "pl") 136#64 lower installed heap allocated
    have binding : allocatedState.locals.lookup (ofString "pl") = some (.val (.word pointer)) := by
      rw [stateEq]
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have kept := rest.keeps (ofString "pl") (by
      intro action member
      exact List.all_eq_true.mp kept_pl action member)
    exact ⟨pointer, low, aligned, room, kept.trans binding⟩

end InitECandidate.Solver.Input.CurrentStartup.PayloadCut

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCut.source_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCut.actions_safe
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCut.kept_pl
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCut.actions_heap
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCut.reached
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCut.record_pointer
