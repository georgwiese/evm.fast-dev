import InitECandidate.Solver.Input.UDivMod.Loop

namespace InitECandidate.Solver.Input.CeilLog2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_ceil_log2 with | .function fn=>progToHOL fn.body | _=>.skip
def test : ExpHOL 64 := .cmp .lower (.shift .lsl (.const 1#64) (localVar "d")) (localVar "n")
def increment : ExpHOL 64 := .op .add [localVar "d",.const 1#64]
def loopBody : ProgHOL 64 := .assign .local (ofString "d") increment
def loop : ProgHOL 64 := .while test loopBody
def finish : ProgHOL 64 := .return (localVar "d")

theorem body_shape : body=.dec (ofString "d") .one (.const 0#64) (.seq loop finish) := by
  simp only [body,Guest.guestFn_ceil_log2,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    loop,test,loopBody,increment,finish,localVar]

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) [DecidablePred source.memaddrs] (n : BitVec 64) (index : Nat)
    (small : index<64) (d : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))))
    (number : source.locals.lookup (ofString "n")=some (.val (.word n))) :
    evalHOLFinite source test=some (.val (.word (if 2^index<n.toNat then 1#64 else 0#64))) := by
  classical
  have encoded : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have powerBound : 2^index<2^64 := Nat.pow_lt_pow_of_lt (by decide) small
  have shifted : ((1#64 : BitVec 64)<<<index).toNat=2^index := by
    simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    exact powerBound
  have invalid : ¬(index≠0 ∧ 64≤index) := by omega
  rw [UDivMod.finite_eval]
  simp [eval,test,localVar,evalHOLExact,toExact,d,number,wordShiftHOL,encoded,invalid,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,shifted]

theorem step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (d : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index)))) :
    evaluateHOLFiniteState source loopBody=(none,bind source "d" (BitVec.ofNat 64 (index+1))) := by
  have read : eval source increment=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,increment,localVar,evalHOLExact,evalListHOLExact,toExact,d,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  exact WitnessRadix.StateSteps.assign_execute source "d" increment _ _ d read

/-- The original increasing shift loop terminates within the supplied bit
width, retaining its minimal power-of-two ceiling and the actual state. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : BitVec 64) (depth index : Nat)
    (depthSmall : depth<64) (inside : index≤depth) (bounded : n.toNat≤2^depth) (enough : depth-index≤source.clock)
    (d : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))))
    (number : source.locals.lookup (ofString "n")=some (.val (.word n))) :
    ∃ target final paid,paid≤depth-index ∧ final=index+paid ∧ final≤depth ∧ n.toNat≤2^final ∧
      (index<final→2^(final-1)<n.toNat) ∧ evaluateHOLFiniteState source loop=(none,target) ∧
      target={source with locals:=target.locals,clock:=source.clock-paid} ∧
      target.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 final))) ∧
      (∀ name : MlS,name≠ofString "d"→target.locals.lookup name=source.locals.lookup name) := by
  classical
  generalize rankEq : depth-index=remaining at enough ⊢
  induction remaining generalizing source index with
  | zero =>
    have atEnd : index=depth := by omega
    have inactive : ¬2^index<n.toNat := by rw [atEnd]; omega
    have read := test_read source n index (by omega) d number
    refine ⟨source,index,0,by omega,by omega,inside,by omega,(by omega),?_,by simp,d,(by intros; rfl)⟩
    rw [loop,evaluateHOLFiniteState_while_total,read]
    simp [inactive]
  | succ remaining ih =>
    by_cases active : 2^index<n.toNat
    · have nextInside : index+1≤depth := by
        by_contra impossible
        have atEnd : index=depth := by omega
        rw [atEnd] at active
        omega
      let entry := decClockHOLFinite source
      let next := bind entry "d" (BitVec.ofNat 64 (index+1))
      have nextClock : next.clock=source.clock-1 := rfl
      have nextN : next.locals.lookup (ofString "n")=some (.val (.word n)) := (bind_lookup_other entry "d" "n" _ (by decide)).trans number
      obtain ⟨target,final,paid,paidBound,finalEq,finalBound,ceiling,previous,tailRun,targetEq,finalD,others⟩ :=
        ih next (index+1) nextInside (bind_lookup_same entry "d" _) nextN (by omega) (by change remaining≤source.clock-1; omega)
      have bodyRun := step_execute entry index d
      have targetClock : target.clock=next.clock-paid := congrArg PanSemStateFiniteExact.clock targetEq
      have read := test_read source n index (by omega) d number
      refine ⟨target,final,paid+1,by omega,by omega,finalBound,ceiling,?_,?_,?_,finalD,?_⟩
      · intro positive
        by_cases later : index+1<final
        · exact previous later
        · have same : final-1=index := by omega
          rw [same]; exact active
      · rw [loop,evaluateHOLFiniteState_while_total,read]
        simp only [if_pos active]
        simp only [if_neg (show source.clock≠0 by omega)]
        rw [bodyRun,WitnessRadix.StateSteps.fixed_clock entry next none (Nat.le_refl _)]
        split
        · exact tailRun
        · rename_i impossible
          exact (impossible (by decide)).elim
      · change target={source with locals:=target.locals,clock:=source.clock-1-paid} at targetEq
        have subtract : source.clock-1-paid=source.clock-(paid+1) := by omega
        simpa only [subtract] using targetEq
      · intro name different
        exact (others name different).trans (by
          change (bind entry "d" _).locals.lookup name=source.locals.lookup name
          simp [WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm different,entry,decClockHOLFinite])
    · have read := test_read source n index (by omega) d number
      refine ⟨source,index,0,by omega,by omega,inside,by omega,(by omega),?_,by simp,d,(by intros; rfl)⟩
      rw [loop,evaluateHOLFiniteState_while_total,read]
      simp [active]

end InitECandidate.Solver.Input.CeilLog2

#print axioms InitECandidate.Solver.Input.CeilLog2.body_shape
#print axioms InitECandidate.Solver.Input.CeilLog2.test_read
#print axioms InitECandidate.Solver.Input.CeilLog2.step_execute
#print axioms InitECandidate.Solver.Input.CeilLog2.loop_execute
