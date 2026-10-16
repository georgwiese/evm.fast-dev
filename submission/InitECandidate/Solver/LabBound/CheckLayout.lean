import InitECandidate.Solver.LabBound.Layout

/-! A computable syntax check whose truth is proved by the Lean kernel. -/
namespace InitECandidate.Solver.LabBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget

def lineFits {width : Nat} [NeZero width] (limit : Nat) : LabLineHOL width → Bool
  | .label _ _ length => length == 0
  | .asm _ bytes _ => decide (bytes.length ≤ limit)
  | .labAsm .install _ _ _ => false
  | .labAsm _ _ bytes _ => decide (bytes.length ≤ limit)

def sectionFits {width : Nat} [NeZero width] (limit : Nat)
    (sec : LabSectionHOL width) : Bool := sec.lines.all (lineFits limit)

theorem lineFits_spec {width : Nat} [NeZero width] (limit : Nat) (line : LabLineHOL width)
    (fits : lineFits limit line = true) :
    labelZero line ∧ lineLength line ≤ limit ∧
      ∀ w bytes n, line ≠ .labAsm .install w bytes n := by
  cases line with
  | label a b length => simp_all [lineFits, labelZero, lineLength]
  | asm a bytes length => simp_all [lineFits, labelZero, lineLength]
  | labAsm a w bytes length => cases a <;> simp_all [lineFits, labelZero, lineLength]

theorem sectionFits_spec {width : Nat} [NeZero width] (limit : Nat)
    (sec : LabSectionHOL width) (fits : sectionFits limit sec = true) :
    secLabelZero sec ∧
    (∀ line ∈ sec.lines, lineLength line ≤ limit) ∧
    (∀ line ∈ sec.lines, ∀ w bytes n, line ≠ .labAsm .install w bytes n) := by
  have all := List.all_eq_true.mp fits
  exact ⟨fun line member => (lineFits_spec limit line (all line member)).1,
    fun line member => (lineFits_spec limit line (all line member)).2.1,
    fun line member => (lineFits_spec limit line (all line member)).2.2⟩

theorem programFits_spec {width : Nat} [NeZero width] (limit : Nat)
    (code : LabProgHOL width) (fits : code.all (sectionFits limit) = true) :
    LineBound code limit ∧ NoInstall code := by
  have all := List.all_eq_true.mp fits
  exact ⟨lineBound_of_lengths code limit
    (fun sec member => (sectionFits_spec limit sec (all sec member)).1)
    (fun sec member => (sectionFits_spec limit sec (all sec member)).2.1),
    noInstall_of_lines code
      (fun sec member => (sectionFits_spec limit sec (all sec member)).2.2)⟩

end InitECandidate.Solver.LabBound

#print axioms InitECandidate.Solver.LabBound.programFits_spec
