import InitECandidate.Solver.Input.OffsetsValidStep

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def walk {F : Type} (source : PanSemStateFiniteExact 64 F) (index : Nat) : Nat→PanSemStateFiniteExact 64 F
  | 0=>source
  | rounds+1=>walk (WitnessRadix.QueryBranch.bind (decClockHOLFinite source) "i" (BitVec.ofNat 64 (index+1))) (index+1) rounds

theorem previous_address (pointer : BitVec 64) (index : Nat) (positive : 0<index) :
    pointer+BitVec.ofNat 64 (8*index)-8#64=pointer+BitVec.ofNat 64 (8*(index-1)) := by
  have arithmetic : 8*index=8*(index-1)+8 := by omega
  rw [arithmetic,BitVec.ofNat_add,←BitVec.add_assoc,BitVec.add_sub_cancel]

/-- Complete literal offset-validation loop on an ordered in-range array.
Each actual current/prior read and both guards are included; only i/clock change. -/
theorem valid_loop {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer fixed total : BitVec 64)
    (values : Nat→BitVec 64) (index count rounds : Nat) (countSmall : count≤8) (finish : index+rounds=count)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (mapped : ∀ position<count,source.memaddrs (pointer+BitVec.ofNat 64 (8*position)))
    (cells : ∀ position<count,source.memory (pointer+BitVec.ofNat 64 (8*position))=.word (values position))
    (lower : ∀ position<count,fixed.toNat≤(values position).toNat)
    (upper : ∀ position<count,(values position).toNat≤total.toNat)
    (ordered : ∀ position<count,0<position→(values (position-1)).toNat≤(values position).toNat)
    (enough : rounds≤source.clock) :
    evaluateHOLFiniteState source loop=(none,walk source index rounds) := by
  classical
  induction rounds generalizing source index with
  | zero=>
    have test:=condition_read source index count (by omega) countSmall indexLocal countLocal
    have inactive : ¬index<count := by omega
    simp only [if_neg inactive] at test
    rw [loop_shape,evaluateHOLFiniteState_while_total,test]
    simp [walk]
  | succ rounds ih=>
    have active : index<count := by omega
    have nonzero : source.clock≠0 := by omega
    let entry:=decClockHOLFinite source
    let next:=WitnessRadix.QueryBranch.bind entry "i" (BitVec.ofNat 64 (index+1))
    have bodyRun:=valid_step entry pointer (values index) fixed total (values (index-1)) index (by omega)
      pointerLocal indexLocal fixedLocal totalLocal (mapped index active) (cells index active) (lower index active) (upper index active)
      (by intro positive; rw [previous_address pointer index positive]; exact mapped (index-1) (by omega))
      (by intro positive; rw [previous_address pointer index positive]; exact cells (index-1) (by omega))
      (ordered index active)
    have nextP : next.locals.lookup (ofString "offs")=some (.val (.word pointer)) :=
      (bind_lookup_other entry "i" "offs" _ (by decide)).trans pointerLocal
    have nextN : next.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))) :=
      (bind_lookup_other entry "i" "n" _ (by decide)).trans countLocal
    have nextF : next.locals.lookup (ofString "fixed")=some (.val (.word fixed)) :=
      (bind_lookup_other entry "i" "fixed" _ (by decide)).trans fixedLocal
    have nextL : next.locals.lookup (ofString "len")=some (.val (.word total)) :=
      (bind_lookup_other entry "i" "len" _ (by decide)).trans totalLocal
    have tailRun:=ih next (index+1) (by omega) nextP (bind_lookup_same _ _ _) nextN nextF nextL
      mapped cells (by change rounds≤source.clock-1; omega)
    have test:=condition_read source index count (by omega) countSmall indexLocal countLocal
    simp only [if_pos active] at test
    rw [loop_shape,evaluateHOLFiniteState_while_total,test]
    simp only []
    simp only [show (1#64 : BitVec 64)≠0 from by decide,↓reduceIte,if_neg nonzero]
    rw [bodyRun,WitnessRadix.StateSteps.fixed_clock entry next none (Nat.le_refl _)]
    split
    · change evaluateHOLFiniteState next (.while condition loopBody)=(none,walk next (index+1) rounds)
      rw [←loop_shape]
      exact tailRun
    · rename_i impossible
      exact (impossible (by decide)).elim

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.previous_address
#print axioms InitECandidate.Solver.Input.Offsets.valid_loop
