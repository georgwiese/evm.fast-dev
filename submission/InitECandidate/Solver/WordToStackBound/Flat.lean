import InitECandidate.Solver.WordToStackBound.Common

namespace InitECandidate.Solver.WordToStackBound.Flat
open Flapjack Flapjack.Compiler.Encoders.Asm

theorem compCorrectAssign {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit name : Nat) (expression : WordLangExpHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.assign name expression) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have flat := premises.2.2.2.2.1
  simp only [flatExpConventions, Bool.false_eq_true] at flat

theorem compCorrectStore {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (address : WordLangExpHOL (BitVec width)) (value : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.store address value) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have flat := premises.2.2.2.2.1
  simp only [flatExpConventions, Bool.false_eq_true] at flat

theorem compCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit pointer length dataPointer dataLength : Nat)
    (names : WordLangCutsetsHOL) (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.install pointer length dataPointer dataLength names) source := by
  intro safe supported
  simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.false_eq_true] at supported

end InitECandidate.Solver.WordToStackBound.Flat
#print axioms InitECandidate.Solver.WordToStackBound.Flat.compCorrectAssign
#print axioms InitECandidate.Solver.WordToStackBound.Flat.compCorrectStore
#print axioms InitECandidate.Solver.WordToStackBound.Flat.compCorrectInstall
