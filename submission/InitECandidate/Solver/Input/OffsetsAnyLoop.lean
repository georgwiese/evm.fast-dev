import InitECandidate.Solver.Input.OffsetsUnroll

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real validator loop on arbitrary mapped offset words. It either
finishes with the exact ordinary walk or raises SszErr10/11 within rounds+1
clocks. No range, ordering or schema validity is assumed. -/
theorem any_loop {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer fixed total : BitVec 64)
    (values : Nat→BitVec 64) (index count rounds : Nat) (small : count≤8) (finish : index+rounds=count)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (mapped : ∀ position<count,source.memaddrs (pointer+BitVec.ofNat 64 (8*position)))
    (cells : ∀ position<count,source.memory (pointer+BitVec.ofNat 64 (8*position))=.word (values position))
    (lookup : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : rounds+1≤source.clock) :
    ∃ result target,evaluateHOLFiniteState source loop=(result,target) ∧
      ((result=none ∧ target=walk source index rounds) ∨
        ∃ code : BitVec 64,∃ paid : Nat,(code=10#64 ∨ code=11#64) ∧
          result=some (.exception (ofString "SszErr") (.val (.word code))) ∧ paid≤rounds+1 ∧
          emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid}) := by
  classical
  induction rounds generalizing source index with
  | zero=>
    have test:=condition_read source index count (by omega) small indexLocal countLocal
    have inactive : ¬index<count := by omega
    simp only [if_neg inactive] at test
    refine ⟨none,source,?_,Or.inl ⟨rfl,rfl⟩⟩
    rw [loop_shape,evaluateHOLFiniteState_while_total,test]
    simp
  | succ rounds ih=>
    have active : index<count := by omega
    have nonzero : source.clock≠0 := by omega
    let entry:=decClockHOLFinite source
    have priorMap : 0<index→entry.memaddrs (pointer+BitVec.ofNat 64 (8*index)-8#64) := by
      intro positive
      rw [previous_address pointer index positive]
      exact mapped (index-1) (by omega)
    have priorCell : 0<index→entry.memory (pointer+BitVec.ofNat 64 (8*index)-8#64)=.word (values (index-1)) := by
      intro positive
      rw [previous_address pointer index positive]
      exact cells (index-1) (by omega)
    by_cases bad : ((values index).toNat<fixed.toNat ∨ total.toNat<(values index).toNat) ∨
        (0<index ∧ (values index).toNat<(values (index-1)).toNat)
    · obtain ⟨code,allowed,bodyRun⟩:=fault_step entry pointer (values index) fixed total (values (index-1)) index (by omega)
        pointerLocal indexLocal fixedLocal totalLocal (mapped index active) (cells index active)
        priorMap priorCell bad lookup exceptionShape (by change 1≤source.clock-1; omega)
      let target:=restore entry "o" (emptyLocalsHOLFinite {entry with clock:=entry.clock-1})
      have run:=active_unroll source target index count small active indexLocal countLocal nonzero
        (some (.exception (ofString "SszErr") (.val (.word code)))) bodyRun (by change source.clock-1-1≤source.clock-1; omega)
      refine ⟨_,target,run,Or.inr ⟨code,2,allowed,rfl,by omega,?_⟩⟩
      change emptyLocalsHOLFinite {source with clock:=source.clock-1-1}=emptyLocalsHOLFinite {source with clock:=source.clock-2}
      have clock : source.clock-1-1=source.clock-2 := by omega
      rw [clock]
    · let next:=WitnessRadix.QueryBranch.bind entry "i" (BitVec.ofNat 64 (index+1))
      have lower : fixed.toNat≤(values index).toNat := by omega
      have upper : (values index).toNat≤total.toNat := by omega
      have ordered : 0<index→(values (index-1)).toNat≤(values index).toNat := by omega
      have bodyRun:=valid_step entry pointer (values index) fixed total (values (index-1)) index (by omega)
        pointerLocal indexLocal fixedLocal totalLocal (mapped index active) (cells index active) lower upper priorMap priorCell ordered
      have nextP : next.locals.lookup (ofString "offs")=some (.val (.word pointer)) :=
        (bind_lookup_other entry "i" "offs" _ (by decide)).trans pointerLocal
      have nextN : next.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))) :=
        (bind_lookup_other entry "i" "n" _ (by decide)).trans countLocal
      have nextF : next.locals.lookup (ofString "fixed")=some (.val (.word fixed)) :=
        (bind_lookup_other entry "i" "fixed" _ (by decide)).trans fixedLocal
      have nextL : next.locals.lookup (ofString "len")=some (.val (.word total)) :=
        (bind_lookup_other entry "i" "len" _ (by decide)).trans totalLocal
      obtain ⟨result,target,tailRun,outcome⟩:=ih next (index+1) (by omega) nextP (bind_lookup_same _ _ _) nextN nextF nextL
        mapped cells lookup exceptionShape (by change rounds+1≤source.clock-1; omega)
      have run:=active_unroll source next index count small active indexLocal countLocal nonzero none bodyRun (Nat.le_refl _)
      change evaluateHOLFiniteState source loop=evaluateHOLFiniteState next loop at run
      rw [tailRun] at run
      refine ⟨result,target,run,?_⟩
      rcases outcome with normal|fault
      · exact Or.inl ⟨normal.1,normal.2⟩
      · obtain ⟨code,paid,allowed,exception,bound,frame⟩:=fault
        refine Or.inr ⟨code,paid+1,allowed,exception,by omega,?_⟩
        rw [frame]
        change emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}=emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)}
        have clock : source.clock-1-paid=source.clock-(paid+1) := by omega
        rw [clock]

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.any_loop
