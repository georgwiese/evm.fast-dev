import InitECandidate.Solver.Mpt.CollapseBranchScanModel
import InitECandidate.Solver.Mpt.CollapseBranchScanCost
import InitECandidate.Solver.Input.LoopInvariantNoControl
import InitECandidate.Solver.Input.LoopNormalExit

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem ScanModel.test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (model : ScanModel source node) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) scanTest=
      some (.val (.word (if model.index.toNat<16 then 1#64 else 0#64))) := by
  have small : model.index.toNat<9223372036854775808:=by have bounded:=model.bounded; omega
  simp [scanTest,localVar,evalHOLFinite,evalHOLExact,toExact,model.counterCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,small]

/-- An actual normal fixed sixteen-child scan retains every nonlocal
field and finishes at16. Its selected index, count and nonnull selected
child are derived from the real load/conditional/assignment steps. -/
theorem scan_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (initial : ScanModel source node)
    (children : ∀ index<16,∃ child : BitVec 64,source.memaddrs (node+32#64+BitVec.ofNat 64 index*8#64) ∧
      source.memory (node+32#64+BitVec.ofNat 64 index*8#64)=.word child)
    (normal : evaluateHOLFiniteState source scan=(none,post)) :
    Input.LocalEffects.erase post=Input.LocalEffects.erase source ∧ ∃ finished : ScanModel post node,finished.index.toNat=16 := by
  classical
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    Input.LocalEffects.erase current=Input.LocalEffects.erase source ∧ Nonempty (ScanModel current node)
  have safe:=scan_body_safe (ofString "node") (by decide) (by decide) (by decide)
  have control (current : PanSemStateFiniteExact 64 Guest.HostMemory) :
      (evaluateHOLFiniteState current scanBody).1≠some .break ∧ (evaluateHOLFiniteState current scanBody).1≠some .continue:=
    (safe.summary_full current).2.2
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ observed,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) scanTest=some (.val (.word observed)) →
      observed≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) scanBody=(none,target) → invariant target:=by
    intro current codeEq actual observed read nonzero funded target run
    obtain ⟨frame,⟨model⟩⟩:=actual
    have active : model.index.toNat<16:=by
      by_contra inactive
      have expected:=model.test_read current node
      rw [if_neg inactive] at expected
      have zero : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero zero
    have memory:=Input.LocalEffects.memory_of_erase source current frame
    have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
    change current.memaddrs=source.memaddrs at domain
    obtain ⟨child,mapped,stored⟩:=children model.index.toNat active
    have word : BitVec.ofNat 64 model.index.toNat=model.index:=by simp
    rw [word] at mapped stored
    have currentMapped : current.memaddrs (node+32#64+model.index*8#64):=by rw [domain]; exact mapped
    have currentStored : current.memory (node+32#64+model.index*8#64)=.word child:=by rw [memory]; exact stored
    let ready:=decClockHOLFinite current
    let currentModel : ScanModel ready node:={model with}
    have expected:=scan_step_execute ready node model.index model.count model.selectedIndex child model.nodeCell model.counterCell model.countCell model.indexCell currentMapped currentStored
    have targetEq : target=scanned ready model.index model.count child:=congrArg Prod.snd (run.symm.trans expected)
    rw [targetEq]
    refine ⟨?_,⟨currentModel.step ready node child active currentStored⟩⟩
    have unchanged : Input.LocalEffects.erase (scanned ready model.index model.count child)=Input.LocalEffects.erase current:=by
      unfold scanned
      split <;> rfl
    exact unchanged.trans frame
  have run:=normal
  rw [scan_shapes.1] at run
  obtain ⟨frame,⟨finished⟩⟩:=Input.loop_invariant_no_control source.code scanTest scanBody control invariant transition source post rfl ⟨rfl,⟨initial⟩⟩ run
  have exit:=Input.loop_normal_exit scanTest scanBody (fun current=>(control current).1) source post run
  have expected:=finished.test_read post node
  have stopped : ¬ finished.index.toNat<16:=by
    intro active
    rw [if_pos active] at expected
    have impossible:=exit.symm.trans expected
    simp at impossible
  exact ⟨frame,finished,by have bounded:=finished.bounded; omega⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.ScanModel.test_read
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.scan_normal
