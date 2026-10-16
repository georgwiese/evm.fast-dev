import InitECandidate.Solver.StackRemoveBound.Space
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.FFI

/-! Retain the original Stack-removal simulation and its result-dependent
clock bound. Successful continuation runs need no extra source clock. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.FFI
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

theorem compCorrectFFI {width : Nat} [NeZero width] {C F : Type}
    (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.ffi name ptr len ptr2 len2 ret, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.ffi name ptr len ptr2 len2 ret : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer (.ffi name ptr len ptr2 len2 ret),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change ptr < pointer ∧ len < pointer ∧ ptr2 < pointer ∧ len2 < pointer ∧ ret < pointer at bound
  have ptrEq := RelationLaws.stateRelGetVar jump bounds pointer ptr source target ⟨relation,bound.1⟩
  have lenEq := RelationLaws.stateRelGetVar jump bounds pointer len source target ⟨relation,bound.2.1⟩
  have ptr2Eq := RelationLaws.stateRelGetVar jump bounds pointer ptr2 source target ⟨relation,bound.2.2.1⟩
  have len2Eq := RelationLaws.stateRelGetVar jump bounds pointer len2 source target ⟨relation,bound.2.2.2.1⟩
  have ffiEq : target.ffi = source.ffi :=
    (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
  rw [evaluate_ffi] at sourceRun
  cases readLen : getVar len source with
  | none =>
    simp only [readLen] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some value =>
    cases value with
    | loc block offset =>
      simp only [readLen] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word length1 =>
      cases readPtr : getVar ptr source with
      | none =>
        simp only [readLen, readPtr] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some value =>
        cases value with
        | loc block offset =>
          simp only [readLen, readPtr] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word address1 =>
          cases readLen2 : getVar len2 source with
          | none =>
            simp only [readLen, readPtr, readLen2] at sourceRun
            exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          | some value =>
            cases value with
            | loc block offset =>
              simp only [readLen, readPtr, readLen2] at sourceRun
              exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
            | word length2 =>
              cases readPtr2 : getVar ptr2 source with
              | none =>
                simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
              | some value =>
                cases value with
                | loc block offset =>
                  simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                  exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                | word address2 =>
                  simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                  cases read1 : readBytearrayWordHOL address1 length1.toNat (memLoadByteAuxExact source.memory source.mdomain source.be) with
                  | none =>
                    simp only [read1] at sourceRun
                    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                  | some config =>
                    cases read2 : readBytearrayWordHOL address2 length2.toNat (memLoadByteAuxExact source.memory source.mdomain source.be) with
                    | none =>
                      simp only [read1,read2] at sourceRun
                      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                    | some bytes =>
                      have targetRead1 := BytearrayReads.readBytearrayImp jump bounds pointer length1.toNat address1 source target config ⟨relation,read1⟩
                      have targetRead2 := BytearrayReads.readBytearrayImp jump bounds pointer length2.toNat address2 source target bytes ⟨relation,read2⟩
                      simp only [read1,read2] at sourceRun
                      cases call : callFFIHOL source.ffi (.extCall name) config bytes with
                      | final outcome =>
                        simp only [call] at sourceRun
                        rcases Prod.mk.inj sourceRun with ⟨resultEq,postEq⟩
                        subst result
                        subst postSource
                        refine ⟨0,target, Nat.zero_le _,?_,ffiEq⟩
                        simpa only [comp,Nat.zero_add] using
                          (evaluate_ffi name ptr len ptr2 len2 ret target).trans (by
                            simp only [← lenEq,← ptrEq,← len2Eq,← ptr2Eq,readLen,readPtr,readLen2,readPtr2,targetRead1,targetRead2,ffiEq,call])
                      | ret newFfi newBytes =>
                        simp only [call] at sourceRun
                        rcases Prod.mk.inj sourceRun with ⟨resultEq,postEq⟩
                        subst result
                        subst postSource
                        have returnedLength := callFFILengthHOL source.ffi (.extCall name) config bytes newBytes newFfi call
                        have readLength := readBytearrayWordHOL_length address2 length2.toNat
                          (memLoadByteAuxExact source.memory source.mdomain source.be) bytes read2
                        have writeRead : readBytearrayWordHOL address2 newBytes.length
                            (memLoadByteAuxExact source.memory source.mdomain source.be) = some bytes := by
                          rw [returnedLength,readLength]
                          exact read2
                        refine ⟨0,{target with
                          memory := writeBytearrayExact address2 newBytes target.memory target.mdomain target.be
                          regs := restrictIn target.regs target.ffiSaveRegs
                          fpRegs := HolFiniteMapExact.empty
                          ffi := newFfi}, Nat.zero_le _,?_,?_⟩
                        · simpa only [comp,Nat.zero_add] using
                            (evaluate_ffi name ptr len ptr2 len2 ret target).trans (by
                              simp only [← lenEq,← ptrEq,← len2Eq,← ptr2Eq,readLen,readPtr,readLen2,readPtr2,targetRead1,targetRead2,ffiEq,call])
                        · exact stateRelFfiWriteback jump bounds pointer source target address2 newBytes bytes newFfi relation writeRead

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectFFI
