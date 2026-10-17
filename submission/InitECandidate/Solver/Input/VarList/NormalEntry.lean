import InitECandidate.Solver.Input.VarList.FirstGuards

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem first_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first length limit : BitVec 64)
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source firstTail=(some (.returned value),post)) :
    ¬badFirst first length ∧ (countWord first).toNat≤limit.toNat ∧
      ∃ innerPost,evaluateHOLFiniteState (counted source first) allocationCall=(some (.returned value),innerPost) ∧ post=restore source "count" innerPost := by
  rw [first_guards source first length limit f n l failCode exceptionShape enough] at run
  by_cases bad : badFirst first length
  · simp only [if_pos bad] at run
    have impossible:=congrArg Prod.fst run
    cases impossible
  · simp only [if_neg bad] at run
    by_cases over : limit<countWord first
    · simp only [if_pos over] at run
      have impossible:=congrArg Prod.fst run
      cases impossible
    · simp only [if_neg over] at run
      have result:=congrArg Prod.fst run
      refine ⟨bad,?_,(evaluateHOLFiniteState (counted source first) allocationCall).2,Prod.ext result rfl,(congrArg Prod.snd run).symm⟩
      change ¬limit.toNat<(countWord first).toNat at over
      omega

/-- A genuine normal return of the whole variable-list decoder either returns
its actual empty pair, or derives a positive, aligned, in-slice offset-table
size and reaches its actual allocation call. Mathematical input size is free. -/
theorem normal_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer limit : BitVec 64) (start length : Nat) (heap : Blob.HeapInput source input pointer)
    (inside : start+length≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    (length=0 ∧ value=emptyValue) ∨
      (4≤length ∧ 0<Guest.GasLimit.le32 input start/4 ∧
        4*(Guest.GasLimit.le32 input start/4)=Guest.GasLimit.le32 input start ∧ Guest.GasLimit.le32 input start≤length ∧
        Guest.GasLimit.le32 input start/4≤limit.toNat ∧
        ∃ innerPost,evaluateHOLFiniteState
          (counted (bind source "first" (BitVec.ofNat 64 (Guest.GasLimit.le32 input start))) (BitVec.ofNat 64 (Guest.GasLimit.le32 input start)))
          allocationCall=(some (.returned value),innerPost) ∧
          post=restore source "first" (restore (bind source "first" (BitVec.ofNat 64 (Guest.GasLimit.le32 input start))) "count" innerPost)) := by
  classical
  rw [entry_execute source input pointer start length heap inside p n failCode exceptionShape enough] at run
  by_cases empty : length=0
  · simp only [if_pos empty] at run
    have eq:=congrArg Prod.fst run
    have eqValue : emptyValue=value := by cases eq; rfl
    exact Or.inl ⟨empty,eqValue.symm⟩
  · simp only [if_neg empty] at run
    by_cases short : length<4
    · simp only [if_pos short] at run
      have impossible:=congrArg Prod.fst run
      cases impossible
    · simp only [if_neg short] at run
      let first:=BitVec.ofNat 64 (Guest.GasLimit.le32 input start)
      let entered:=bind source "first" first
      have result:=congrArg Prod.fst run
      have firstRun : evaluateHOLFiniteState entered firstTail=
          (some (.returned value),(evaluateHOLFiniteState entered firstTail).2) := Prod.ext result rfl
      have savedN : entered.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) :=
        (bind_lookup_other source "first" "len" first (by decide)).trans n
      have savedL : entered.locals.lookup (ofString "lim")=some (.val (.word limit)) :=
        (bind_lookup_other source "first" "lim" first (by decide)).trans l
      obtain ⟨valid,limitBound,innerPost,allocationRun,firstPost⟩:=first_normal entered _ first (BitVec.ofNat 64 length) limit
        (bind_lookup_same _ _ _) savedN savedL failCode exceptionShape enough value firstRun
      obtain ⟨positive,aligned,upper⟩:=first_valid first (BitVec.ofNat 64 length) valid
      have firstNat : first.toNat=Guest.GasLimit.le32 input start := RawScalar.le32_number input start
      have extent : input.length%2^64<2^64 := Nat.mod_lt _ (by decide)
      have lengthNat : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      rw [count_number,firstNat] at positive aligned limitBound
      rw [firstNat,lengthNat] at upper
      have postEq:= (congrArg Prod.snd run).symm
      change post=restore source "first" (evaluateHOLFiniteState entered firstTail).2 at postEq
      rw [firstPost] at postEq
      exact Or.inr ⟨by omega,positive,aligned,upper,limitBound,innerPost,allocationRun,postEq⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.first_normal
#print axioms InitECandidate.Solver.Input.VarList.normal_entry
