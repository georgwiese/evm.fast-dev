import InitECandidate.Solver.Rlp.ValidationLoop
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normal loop exit retains the physical arena and pending-stack
invariant. This derives the reached model instead of assuming it. -/
theorem loop_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (rootEnd limit : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (model : Invariant rootEnd limit source)
    (normal : evaluateHOLFiniteState source loop=(none,target)) : Invariant rootEnd limit target := by
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory),
      current.clock=clock → current.code=source.code → Invariant rootEnd limit current →
      evaluateHOLFiniteState current loop=(none,target) → Invariant rootEnd limit target := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro current clockEq codeEq valid run
      obtain ⟨cursor,position,ending,go,frames,view⟩ := valid
      rw [loop_shape] at run
      rcases view.binary with zero | one
      · have goCell := view.goCell
        rw [zero] at goCell
        have read : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) condition=some (.val (.word 0#64)) := by
          simp [evalHOLFinite,condition,evalHOLExact,localVar,toExact,goCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [evaluateHOLFiniteState_while_total,read] at run
        simp only [if_neg (not_not_intro (Eq.refl (0#64 : BitVec 64)))] at run
        have same : target=current := (Prod.mk.inj run).2.symm
        rw [same]
        exact ⟨cursor,position,ending,go,frames,view⟩
      · have goCell := view.goCell
        rw [one] at goCell
        have read : eval current condition=some (.val (.word 1#64)) := by
          simp [eval,condition,evalHOLExact,localVar,toExact,goCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        obtain ⟨positive,middle,bodyRun,tailRun,bodyClock⟩ := Input.while_none_step current target (ofString "p") condition loopBody loop_body_prefix read run
        have activeView : View current rootEnd cursor limit position ending 1#64 frames := by rw [←one]; exact view
        have entryView := View.clock current rootEnd cursor limit position ending 1#64 frames (current.clock-1) activeView
        have next := (loop_body_none (decClockHOLFinite current) middle rootEnd cursor limit position ending frames entryView
          (by change Input.OriginalCode.Installed current.code; rw [codeEq]; exact installed) bodyRun).1
        have middleCode : middle.code=source.code := (Input.evaluation_fields (decClockHOLFinite current) middle loopBody none bodyRun).2.2.2.trans codeEq
        have earlier : middle.clock<clock := by omega
        exact ih middle.clock earlier middle rfl middleCode next (by rw [loop_shape]; exact tailRun)
  exact auxiliary source.clock source rfl rfl model normal

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.loop_none
