import InitECandidate.Solver.Input.OffsetsWalk

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole actual nonempty offset validator, including entry, complete loop,
final fixed-size guard and all scopes. No memory or other nonlocal field changes. -/
theorem valid_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer fixed total : BitVec 64)
    (values : Nat→BitVec 64) (count : Nat) (positive : 0<count) (countSmall : count≤8)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (mapped : ∀ position<count,source.memaddrs (pointer+BitVec.ofNat 64 (8*position)))
    (cells : ∀ position<count,source.memory (pointer+BitVec.ofNat 64 (8*position))=.word (values position))
    (lower : ∀ position<count,fixed.toNat≤(values position).toNat)
    (upper : ∀ position<count,(values position).toNat≤total.toNat)
    (ordered : ∀ position<count,0<position→(values (position-1)).toNat≤(values position).toNat)
    (first : values 0=fixed)
    (lookup : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : count+1≤source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-count} := by
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
  have loopRun:=valid_loop entered pointer fixed total values 0 count count countSmall (by omega)
    p (bind_lookup_same _ _ _) n f l mapped cells lower upper ordered (by change count≤source.clock; omega)
  let finished:=walk entered 0 count
  have frame:=walk_frame entered 0 count
  have pAfter : finished.locals.lookup (ofString "offs")=some (.val (.word pointer)) := by
    rw [walk_other _ _ _ _ (by decide)]
    exact p
  have fAfter : finished.locals.lookup (ofString "fixed")=some (.val (.word fixed)) := by
    rw [walk_other _ _ _ _ (by decide)]
    exact f
  have memory : finished.memory=source.memory := by
    have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.memory) frame
    exact h
  have domain : finished.memaddrs=source.memaddrs := by
    have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.memaddrs) frame
    exact h
  have code : finished.code=source.code := by
    have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.code) frame
    exact h
  have shapes : finished.eshapes=source.eshapes := by
    have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.eshapes) frame
    exact h
  have finalClock : finished.clock=source.clock-count := by
    have h:=congrArg (fun state : PanSemStateFiniteExact 64 F=>state.clock) frame
    exact h
  have tailRun:=tail_execute finished pointer fixed fixed pAfter fAfter
    (by rw [domain]; simpa using mapped 0 positive)
    (by rw [memory]; simpa [first] using cells 0 positive)
    (by rw [code]; exact lookup) (by rw [shapes]; exact exceptionShape) (by rw [finalClock]; omega)
  simp only [if_pos rfl] at tailRun
  have seqRun:=WitnessRadix.StateSteps.next_sequence entered finished loop tailCode loopRun (by change finished.clock≤source.clock; rw [finalClock]; omega)
  rw [tailRun] at seqRun
  have setup : WitnessRadix.BuildEntry.Initializes source [("i",.const 0#64)] entered (fun target=>restore source "i" target) :=
    .step 0#64 rfl (.done _)
  have scopeRun:=WitnessRadix.BuildEntry.declarations_execute setup (.seq loop tailCode)
  rw [seqRun] at scopeRun
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
  refine ⟨restore source "i" (emptyLocalsHOLFinite finished),?_,?_⟩
  · rw [body_shape,WitnessRadix.StateSteps.next_sequence source source _ _ initialGuard (Nat.le_refl _)]
    exact scopeRun
  · exact frame

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.valid_execute
