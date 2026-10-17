import InitECandidate.Solver.Input.VarList.Entry
import InitECandidate.Solver.Input.RawScalar

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def badFirst (first length : BitVec 64) : Prop := first=0#64 ∨ first&&&3#64≠0#64 ∨ length<first
instance badFirstDecidable (first length : BitVec 64) : Decidable (badFirst first length) := by
  unfold badFirst
  infer_instance

def countWord (first : BitVec 64) : BitVec 64 := first >>> (2:Nat)

theorem mask_number (first : BitVec 64) : (first&&&3#64).toNat=first.toNat%4 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod first.toNat 2

theorem first_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first length : BitVec 64)
    (f : source.locals.lookup (ofString "first")=some (.val (.word first)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length))) :
    eval source firstTest=some (.val (.word (if badFirst first length then 1#64 else 0#64))) := by
  classical
  have foldedAnd : ∀ word : BitVec 64,AndOp.and word (AndOp.and 3#64 18446744073709551615#64)=word&&&3#64 := by
    intro word
    have constant : AndOp.and (3#64) (18446744073709551615#64)=3#64 := by decide
    rw [constant]
    rfl
  by_cases z : first=0#64 <;> by_cases a : first&&&3#64=0#64 <;> by_cases over : length<first <;>
    simp [eval,firstTest,badFirst,localVar,evalHOLExact,evalListHOLExact,toExact,f,n,valueIsWord,valueWord,
      wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,foldedAnd,z,a,over,OrOp.or]

theorem count_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first : BitVec 64)
    (f : source.locals.lookup (ofString "first")=some (.val (.word first))) :
    eval source countExpression=some (.val (.word (countWord first))) := by
  classical
  simp [eval,countExpression,localVar,evalHOLExact,toExact,f,wordShiftHOL,countWord]

theorem count_number (first : BitVec 64) : (countWord first).toNat=first.toNat/4 := by
  simp [countWord,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

/-- The real first-offset guard establishes a nonzero, aligned header and
bounds every offset-table read before the allocation and record loop. -/
theorem first_valid (first length : BitVec 64) (valid : ¬badFirst first length) :
    0<(countWord first).toNat ∧ 4*(countWord first).toNat=first.toNat ∧ first.toNat≤length.toNat := by
  have positive : 0<first.toNat := by
    by_contra zero
    have eq : first=0#64 := BitVec.eq_of_toNat_eq (by change first.toNat=0; omega)
    exact valid (Or.inl eq)
  have aligned : first.toNat%4=0 := by
    have mask : first&&&3#64=0#64 := by
      by_contra no
      exact valid (Or.inr (Or.inl no))
    have h:=congrArg BitVec.toNat mask
    rw [mask_number] at h
    exact h
  have upper : first.toNat≤length.toNat := by
    by_contra no
    apply valid
    exact Or.inr (Or.inr (by change length.toNat<first.toNat; omega))
  rw [count_number]
  omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.mask_number
#print axioms InitECandidate.Solver.Input.VarList.first_test_read
#print axioms InitECandidate.Solver.Input.VarList.count_read
#print axioms InitECandidate.Solver.Input.VarList.count_number
#print axioms InitECandidate.Solver.Input.VarList.first_valid
