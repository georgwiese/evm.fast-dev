import InitECandidate.Solver.Input.OffsetsAnyLoop

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole actual nonempty validator on arbitrary mapped offset words. A normal
return establishes the fixed first offset; every rejection raises its actual
SszErr code. All paths preserve memory and pay at most count+1 source clocks. -/
theorem any_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer fixed total : BitVec 64)
    (values : Nat→BitVec 64) (count : Nat) (positive : 0<count) (small : count≤8)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (mapped : ∀ position<count,source.memaddrs (pointer+BitVec.ofNat 64 (8*position)))
    (cells : ∀ position<count,source.memory (pointer+BitVec.ofNat 64 (8*position))=.word (values position))
    (lookup : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : count+1≤source.clock) :
    ∃ result target paid,evaluateHOLFiniteState source body=(result,target) ∧ paid≤count+1 ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} ∧
      ((result=some (.returned (.val (.word 0#64))) ∧ values 0=fixed) ∨
        ∃ code : BitVec 64,(code=10#64 ∨ code=11#64 ∨ code=12#64) ∧
          result=some (.exception (ofString "SszErr") (.val (.word code)))) := by
  classical
  let entered:=WitnessRadix.QueryBranch.bind source "i" 0#64
  have p : entered.locals.lookup (ofString "offs")=some (.val (.word pointer)) :=
    (bind_lookup_other source "i" "offs" _ (by decide)).trans pointerLocal
  have n : entered.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))) :=
    (bind_lookup_other source "i" "n" _ (by decide)).trans countLocal
  have f : entered.locals.lookup (ofString "fixed")=some (.val (.word fixed)) :=
    (bind_lookup_other source "i" "fixed" _ (by decide)).trans fixedLocal
  have l : entered.locals.lookup (ofString "len")=some (.val (.word total)) :=
    (bind_lookup_other source "i" "len" _ (by decide)).trans totalLocal
  have encoded : (BitVec.ofNat 64 count).toNat=count := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nonzero : BitVec.ofNat 64 count≠0#64 := by
    intro equal
    have number:=congrArg BitVec.toNat equal
    rw [encoded] at number
    change count=0 at number
    omega
  have initialGuard : evaluateHOLFiniteState source (.ite (.cmp .equal (localVar "n") (.const 0#64)) returnZero .skip)=(none,source) := by
    rw [evaluateHOLFiniteState_ite]
    simp [localVar,evalHOLExact,toExact,countLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  have setup : WitnessRadix.BuildEntry.Initializes source [("i",.const 0#64)] entered (fun target=>restore source "i" target) :=
    .step 0#64 rfl (.done _)
  have wrap (result : Option (PanSemResultExact 64)) (target : PanSemStateFiniteExact 64 F) (paid : Nat)
      (coreRun : evaluateHOLFiniteState entered (.seq loop tailCode)=(result,target))
      (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid}) :
      ∃ final,evaluateHOLFiniteState source body=(result,final) ∧
        emptyLocalsHOLFinite final=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
    have scopeRun:=WitnessRadix.BuildEntry.declarations_execute setup (.seq loop tailCode)
    rw [coreRun] at scopeRun
    refine ⟨restore source "i" target,?_,frame⟩
    rw [body_shape,WitnessRadix.StateSteps.next_sequence source source _ _ initialGuard (Nat.le_refl _)]
    exact scopeRun
  obtain ⟨result,target,loopRun,outcome⟩:=any_loop entered pointer fixed total values 0 count count small (by omega)
    p (bind_lookup_same _ _ _) n f l mapped cells lookup exceptionShape enough
  rcases outcome with normal|fault
  · rcases normal with ⟨rfl,rfl⟩
    let finished:=walk entered 0 count
    have frame:=walk_frame entered 0 count
    have pAfter : finished.locals.lookup (ofString "offs")=some (.val (.word pointer)) := by
      rw [walk_other _ _ _ _ (by decide)]
      exact p
    have fAfter : finished.locals.lookup (ofString "fixed")=some (.val (.word fixed)) := by
      rw [walk_other _ _ _ _ (by decide)]
      exact f
    have memory : finished.memory=source.memory := by have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.memory) frame; exact h
    have domain : finished.memaddrs=source.memaddrs := by have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.memaddrs) frame; exact h
    have code : finished.code=source.code := by have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.code) frame; exact h
    have shapes : finished.eshapes=source.eshapes := by have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.eshapes) frame; exact h
    have clock : finished.clock=source.clock-count := by have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.clock) frame; exact h
    have tailRun:=tail_execute finished pointer (values 0) fixed pAfter fAfter
      (by rw [domain]; simpa using mapped 0 positive)
      (by rw [memory]; simpa using cells 0 positive)
      (by rw [code]; exact lookup) (by rw [shapes]; exact exceptionShape) (by rw [clock]; omega)
    have core:=WitnessRadix.StateSteps.next_sequence entered finished loop tailCode loopRun (by change finished.clock≤source.clock; rw [clock]; omega)
    rw [tailRun] at core
    by_cases same : values 0=fixed
    · simp only [if_pos same] at core
      obtain ⟨final,run,finalFrame⟩:=wrap _ (emptyLocalsHOLFinite finished) count core frame
      exact ⟨_,final,count,run,by omega,finalFrame,Or.inl ⟨rfl,same⟩⟩
    · simp only [if_neg same] at core
      have finalFrame : emptyLocalsHOLFinite (emptyLocalsHOLFinite {finished with clock:=finished.clock-1})=
          emptyLocalsHOLFinite {source with clock:=source.clock-(count+1)} := by
        change {emptyLocalsHOLFinite finished with clock:=finished.clock-1}=_
        have sourceFrame : emptyLocalsHOLFinite finished=emptyLocalsHOLFinite {source with clock:=source.clock-count} := frame
        rw [sourceFrame,clock]
        change emptyLocalsHOLFinite {source with clock:=source.clock-count-1}=_
        rw [Nat.sub_sub]
      obtain ⟨final,run,frameAfter⟩:=wrap _ _ (count+1) core finalFrame
      exact ⟨_,final,count+1,run,Nat.le_refl _,frameAfter,Or.inr ⟨12#64,Or.inr (Or.inr rfl),rfl⟩⟩
  · obtain ⟨code,paid,allowed,rfl,bound,frame⟩:=fault
    have clock : target.clock=source.clock-paid := by
      have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.clock) frame
      exact h
    have core:=WitnessRadix.StateSteps.stopped_sequence entered target loop tailCode
      (.exception (ofString "SszErr") (.val (.word code))) loopRun (by change target.clock≤source.clock; rw [clock]; omega)
    obtain ⟨final,run,frameAfter⟩:=wrap _ target paid core frame
    refine ⟨_,final,paid,run,bound,frameAfter,Or.inr ⟨code,?_,rfl⟩⟩
    rcases allowed with first|second
    · exact Or.inl first
    · exact Or.inr (Or.inl second)

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.any_execute
