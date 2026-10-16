import InitECandidate.Solver.LabBound.Common
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend

/-! Local syntax checks sufficient for the static-program cost premises. -/
namespace InitECandidate.Solver.LabBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps

/-- A bound on individual encoded lines, with zero-width labels, bounds every
physical successor displacement used by the recursive simulation. -/
theorem lineBound_of_lengths {width : Nat} [NeZero width] (code : LabProgHOL width)
    (limit : Nat) (zeros : ∀ sec ∈ code, secLabelZero sec)
    (sizes : ∀ sec ∈ code, ∀ line ∈ sec.lines, lineLength line ≤ limit) :
    LineBound code limit := by
  have general : ∀ pc pos, posVal (pc + 1) pos code ≤ posVal pc pos code + limit := by
    intro pc pos
    induction code generalizing pc pos with
    | nil => simp [posVal]
    | cons sec rest ih =>
      rcases sec with ⟨key, lines⟩
      have zr : ∀ sec ∈ rest, secLabelZero sec := fun sec hm => zeros sec (by simp [hm])
      have sr : ∀ sec ∈ rest, ∀ line ∈ sec.lines, lineLength line ≤ limit :=
        fun sec hm => sizes sec (by simp [hm])
      have zl : ∀ line ∈ lines, labelZero line := zeros ⟨key, lines⟩ (by simp)
      have sl : ∀ line ∈ lines, lineLength line ≤ limit := sizes ⟨key, lines⟩ (by simp)
      clear zeros sizes
      induction lines generalizing pc pos with
      | nil => simpa only [posVal] using ih zr sr pc pos
      | cons line lines ihl =>
        have zh := zl line (by simp)
        have sh := sl line (by simp)
        have zt : ∀ line ∈ lines, labelZero line := fun line hm => zl line (by simp [hm])
        have st : ∀ line ∈ lines, lineLength line ≤ limit := fun line hm => sl line (by simp [hm])
        have zcode : ∀ sec ∈ (⟨key, lines⟩ :: rest : LabProgHOL width), secLabelZero sec := by
          intro sec member
          rcases List.mem_cons.mp member with rfl | member
          · exact zt
          · exact zr sec member
        cases line with
        | label a b length =>
          simp only [labelZero] at zh
          simp only [posVal, isLabelHOL, reduceIte, lineLength, zh, Nat.add_zero]
          exact ihl pc pos zt st
        | asm a bytes length =>
          cases pc with
          | zero =>
            simp only [posVal, isLabelHOL, Bool.false_eq_true, reduceIte, Nat.zero_add,
              Nat.one_ne_zero, Nat.sub_self, lineLength]
            rw [secLabelZero_posVal_zero _ _ zcode]
            exact Nat.add_le_add_left sh pos
          | succ pc =>
            simpa only [posVal, isLabelHOL, Bool.false_eq_true, reduceIte,
              Nat.succ_ne_zero, Nat.add_one_sub_one, lineLength] using
              ihl pc (pos + bytes.length) zt st
        | labAsm a w bytes length =>
          cases pc with
          | zero =>
            simp only [posVal, isLabelHOL, Bool.false_eq_true, reduceIte, Nat.zero_add,
              Nat.one_ne_zero, Nat.sub_self, lineLength]
            rw [secLabelZero_posVal_zero _ _ zcode]
            exact Nat.add_le_add_left sh pos
          | succ pc =>
            simpa only [posVal, isLabelHOL, Bool.false_eq_true, reduceIte,
              Nat.succ_ne_zero, Nat.add_one_sub_one, lineLength] using
              ihl pc (pos + bytes.length) zt st
  exact fun pc => general pc 0

/-- Syntactic absence of Install is sufficient at every source position. -/
theorem noInstall_of_lines {width : Nat} [NeZero width] (code : LabProgHOL width)
    (safe : ∀ sec ∈ code, ∀ line ∈ sec.lines, ∀ w bytes n,
      line ≠ .labAsm .install w bytes n) : NoInstall code := by
  intro pc w bytes n
  induction code generalizing pc with
  | nil => simp [asmFetchAux]
  | cons sec rest ih =>
    rcases sec with ⟨key, lines⟩
    have sr : ∀ sec ∈ rest, ∀ line ∈ sec.lines, ∀ w bytes n,
        line ≠ .labAsm .install w bytes n := fun sec hm => safe sec (by simp [hm])
    have sl : ∀ line ∈ lines, ∀ w bytes n, line ≠ .labAsm .install w bytes n :=
      safe ⟨key, lines⟩ (by simp)
    clear safe
    induction lines generalizing pc with
    | nil => simpa only [asmFetchAux] using ih sr pc
    | cons line lines ihl =>
      have sh := sl line (by simp) w bytes n
      have st : ∀ line ∈ lines, ∀ w bytes n, line ≠ .labAsm .install w bytes n :=
        fun line hm => sl line (by simp [hm])
      rw [asmFetchAux]
      split
      · exact ihl pc st
      · split
        · intro equality
          exact sh (Option.some.inj equality)
        · exact ihl (pc - 1) st

/-- Compiler code similarity preserves absence of dynamic installation. -/
theorem noInstall_of_similar {width : Nat} [NeZero width]
    (source target : LabProgHOL width) (similar : codeSimilar source target)
    (static : NoInstall target) : NoInstall source := by
  intro pc w bytes n fetch
  have related := codeSimilar_asmFetchAux pc source target similar
  rw [fetch] at related
  cases found : asmFetchAux pc target with
  | none => rw [found] at related; cases related
  | some line =>
    rw [found] at related
    cases related with
    | some related =>
      cases line with
      | label => cases related
      | asm => cases related
      | labAsm a w' bytes' n' =>
        simp only [lineSimilar] at related
        subst a
        exact static pc w' bytes' n' found

end InitECandidate.Solver.LabBound

#print axioms InitECandidate.Solver.LabBound.lineBound_of_lengths
#print axioms InitECandidate.Solver.LabBound.noInstall_of_lines
#print axioms InitECandidate.Solver.LabBound.noInstall_of_similar
