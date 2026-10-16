import InitECandidate.Solver.GuestWork.ZeroStoreProgram
import InitECandidate.Proofs.BackendStages.Named78

namespace InitECandidate.Solver.GuestWork.MemzeroMemory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open ZeroMemory
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The complete fixed memzero routine never increases an existing word's
unsigned value. Covers all executions, including failed stores and timeouts;
no alignment, address separation, initial registers or length bound is assumed. -/
theorem clears {C F : Type} : Clears (C := C) (F := F) Named78.2 := by
  apply Clears.seq
  ·
    exact Clears.leaf _ (by decide)
  ·
    apply Clears.seq
    ·
      exact Clears.leaf _ (by decide)
    ·
      apply Clears.seq
      ·
        exact Clears.leaf _ (by decide)
      ·
        apply Clears.seq
        ·
          exact Clears.leaf _ (by decide)
        ·
          apply Clears.seq
          ·
            exact Clears.leaf _ (by decide)
          ·
            apply Clears.seq
            ·
              exact Clears.leaf _ (by decide)
            ·
              apply Clears.seq
              ·
                apply Clears.ite
                ·
                  apply Clears.seq
                  ·
                    exact Clears.leaf _ (by decide)
                  ·
                    apply Clears.seq
                    ·
                      exact Clears.leaf _ (by decide)
                    ·
                      apply Clears.seq
                      ·
                        exact Clears.leaf _ (by decide)
                      ·
                        apply Clears.seq
                        ·
                          apply Clears.loop
                          apply Clears.seq
                          ·
                            exact Clears.leaf _ (by decide)
                          ·
                            apply Clears.seq
                            ·
                              exact Clears.leaf _ (by decide)
                            ·
                              apply Clears.seq
                              ·
                                apply Clears.ite
                                ·
                                  apply Clears.seq
                                  ·
                                    exact Clears.leaf _ (by decide)
                                  ·
                                    apply Clears.seq
                                    ·
                                      exact Clears.leaf _ (by decide)
                                    ·
                                      apply Clears.seq
                                      ·
                                        exact Clears.leaf _ (by decide)
                                      ·
                                        apply Clears.skipAfter
                                        apply Clears.wordStoreThen
                                        apply Clears.seq
                                        ·
                                          exact Clears.leaf _ (by decide)
                                        ·
                                          apply Clears.seq
                                          ·
                                            exact Clears.leaf _ (by decide)
                                          ·
                                            apply Clears.skipAfter
                                            apply Clears.wordStoreThen
                                            apply Clears.seq
                                            ·
                                              exact Clears.leaf _ (by decide)
                                            ·
                                              apply Clears.seq
                                              ·
                                                exact Clears.leaf _ (by decide)
                                              ·
                                                apply Clears.skipAfter
                                                apply Clears.wordStoreThen
                                                apply Clears.seq
                                                ·
                                                  exact Clears.leaf _ (by decide)
                                                ·
                                                  apply Clears.seq
                                                  ·
                                                    exact Clears.leaf _ (by decide)
                                                  ·
                                                    apply Clears.skipAfter
                                                    apply Clears.wordStoreThen
                                                    apply Clears.seq
                                                    ·
                                                      exact Clears.leaf _ (by decide)
                                                    ·
                                                      exact Clears.leaf _ (by decide)
                                ·
                                  apply Clears.seq
                                  ·
                                    exact Clears.leaf _ (by decide)
                                  ·
                                    apply Clears.seq
                                    ·
                                      exact Clears.leaf _ (by decide)
                                    ·
                                      exact Clears.leaf _ (by decide)
                              ·
                                apply Clears.seq
                                ·
                                  exact Clears.leaf _ (by decide)
                                ·
                                  exact Clears.leaf _ (by decide)
                        ·
                          apply Clears.seq
                          ·
                            exact Clears.leaf _ (by decide)
                          ·
                            apply Clears.seq
                            ·
                              exact Clears.leaf _ (by decide)
                            ·
                              apply Clears.seq
                              ·
                                exact Clears.leaf _ (by decide)
                              ·
                                apply Clears.seq
                                ·
                                  apply Clears.loop
                                  apply Clears.seq
                                  ·
                                    exact Clears.leaf _ (by decide)
                                  ·
                                    apply Clears.seq
                                    ·
                                      exact Clears.leaf _ (by decide)
                                    ·
                                      apply Clears.seq
                                      ·
                                        apply Clears.ite
                                        ·
                                          apply Clears.seq
                                          ·
                                            exact Clears.leaf _ (by decide)
                                          ·
                                            apply Clears.seq
                                            ·
                                              exact Clears.leaf _ (by decide)
                                            ·
                                              apply Clears.seq
                                              ·
                                                exact Clears.leaf _ (by decide)
                                              ·
                                                apply Clears.skipAfter
                                                apply Clears.wordStoreThen
                                                apply Clears.seq
                                                ·
                                                  exact Clears.leaf _ (by decide)
                                                ·
                                                  exact Clears.leaf _ (by decide)
                                        ·
                                          apply Clears.seq
                                          ·
                                            exact Clears.leaf _ (by decide)
                                          ·
                                            apply Clears.seq
                                            ·
                                              exact Clears.leaf _ (by decide)
                                            ·
                                              exact Clears.leaf _ (by decide)
                                      ·
                                        apply Clears.seq
                                        ·
                                          exact Clears.leaf _ (by decide)
                                        ·
                                          exact Clears.leaf _ (by decide)
                                ·
                                  apply Clears.seq
                                  ·
                                    exact Clears.leaf _ (by decide)
                                  ·
                                    exact Clears.leaf _ (by decide)
                ·
                  apply Clears.seq
                  ·
                    exact Clears.leaf _ (by decide)
                  ·
                    exact Clears.leaf _ (by decide)
              ·
                apply Clears.seq
                ·
                  exact Clears.leaf _ (by decide)
                ·
                  apply Clears.seq
                  ·
                    exact Clears.leaf _ (by decide)
                  ·
                    apply Clears.seq
                    ·
                      exact Clears.leaf _ (by decide)
                    ·
                      apply Clears.seq
                      ·
                        apply Clears.loop
                        apply Clears.seq
                        ·
                          exact Clears.leaf _ (by decide)
                        ·
                          apply Clears.seq
                          ·
                            exact Clears.leaf _ (by decide)
                          ·
                            apply Clears.seq
                            ·
                              apply Clears.ite
                              ·
                                apply Clears.seq
                                ·
                                  exact Clears.leaf _ (by decide)
                                ·
                                  apply Clears.seq
                                  ·
                                    exact Clears.leaf _ (by decide)
                                  ·
                                    apply Clears.seq
                                    ·
                                      exact Clears.leaf _ (by decide)
                                    ·
                                      apply Clears.byteStoreThen
                                      apply Clears.seq
                                      ·
                                        exact Clears.leaf _ (by decide)
                                      ·
                                        apply Clears.seq
                                        ·
                                          exact Clears.leaf _ (by decide)
                                        ·
                                          apply Clears.byteStoreThen
                                          apply Clears.seq
                                          ·
                                            exact Clears.leaf _ (by decide)
                                          ·
                                            apply Clears.seq
                                            ·
                                              exact Clears.leaf _ (by decide)
                                            ·
                                              apply Clears.byteStoreThen
                                              apply Clears.seq
                                              ·
                                                exact Clears.leaf _ (by decide)
                                              ·
                                                apply Clears.seq
                                                ·
                                                  exact Clears.leaf _ (by decide)
                                                ·
                                                  apply Clears.byteStoreThen
                                                  apply Clears.seq
                                                  ·
                                                    exact Clears.leaf _ (by decide)
                                                  ·
                                                    apply Clears.seq
                                                    ·
                                                      exact Clears.leaf _ (by decide)
                                                    ·
                                                      apply Clears.byteStoreThen
                                                      apply Clears.seq
                                                      ·
                                                        exact Clears.leaf _ (by decide)
                                                      ·
                                                        apply Clears.seq
                                                        ·
                                                          exact Clears.leaf _ (by decide)
                                                        ·
                                                          apply Clears.byteStoreThen
                                                          apply Clears.seq
                                                          ·
                                                            exact Clears.leaf _ (by decide)
                                                          ·
                                                            apply Clears.seq
                                                            ·
                                                              exact Clears.leaf _ (by decide)
                                                            ·
                                                              apply Clears.byteStoreThen
                                                              apply Clears.seq
                                                              ·
                                                                exact Clears.leaf _ (by decide)
                                                              ·
                                                                apply Clears.seq
                                                                ·
                                                                  exact Clears.leaf _ (by decide)
                                                                ·
                                                                  apply Clears.byteStoreThen
                                                                  apply Clears.seq
                                                                  ·
                                                                    exact Clears.leaf _ (by decide)
                                                                  ·
                                                                    exact Clears.leaf _ (by decide)
                              ·
                                apply Clears.seq
                                ·
                                  exact Clears.leaf _ (by decide)
                                ·
                                  apply Clears.seq
                                  ·
                                    exact Clears.leaf _ (by decide)
                                  ·
                                    exact Clears.leaf _ (by decide)
                            ·
                              apply Clears.seq
                              ·
                                exact Clears.leaf _ (by decide)
                              ·
                                exact Clears.leaf _ (by decide)
                      ·
                        apply Clears.seq
                        ·
                          exact Clears.leaf _ (by decide)
                        ·
                          apply Clears.seq
                          ·
                            exact Clears.leaf _ (by decide)
                          ·
                            apply Clears.seq
                            ·
                              exact Clears.leaf _ (by decide)
                            ·
                              apply Clears.seq
                              ·
                                apply Clears.loop
                                apply Clears.seq
                                ·
                                  exact Clears.leaf _ (by decide)
                                ·
                                  apply Clears.seq
                                  ·
                                    apply Clears.ite
                                    ·
                                      apply Clears.seq
                                      ·
                                        exact Clears.leaf _ (by decide)
                                      ·
                                        apply Clears.seq
                                        ·
                                          exact Clears.leaf _ (by decide)
                                        ·
                                          apply Clears.seq
                                          ·
                                            exact Clears.leaf _ (by decide)
                                          ·
                                            apply Clears.byteStoreThen
                                            apply Clears.seq
                                            ·
                                              exact Clears.leaf _ (by decide)
                                            ·
                                              apply Clears.seq
                                              ·
                                                exact Clears.leaf _ (by decide)
                                              ·
                                                apply Clears.seq
                                                ·
                                                  exact Clears.leaf _ (by decide)
                                                ·
                                                  exact Clears.leaf _ (by decide)
                                    ·
                                      apply Clears.seq
                                      ·
                                        exact Clears.leaf _ (by decide)
                                      ·
                                        exact Clears.leaf _ (by decide)
                                  ·
                                    apply Clears.seq
                                    ·
                                      exact Clears.leaf _ (by decide)
                                    ·
                                      exact Clears.leaf _ (by decide)
                              ·
                                apply Clears.seq
                                ·
                                  exact Clears.leaf _ (by decide)
                                ·
                                  apply Clears.seq
                                  ·
                                    exact Clears.leaf _ (by decide)
                                  ·
                                    apply Clears.seq
                                    ·
                                      exact Clears.leaf _ (by decide)
                                    ·
                                      exact Clears.leaf _ (by decide)

/-- A saved word length remains a word below its original upper bound across
an actual memzero execution, even when the zeroing region overlaps that slot. -/
theorem saved_length {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (address : BitVec 64) (maximum : Nat)
    (bounded : ∃ value, source.memory address = .word value ∧ value.toNat ≤ maximum)
    (execution : evaluate (Named78.2, source) = (result, post)) :
    ∃ value, post.memory address = .word value ∧ value.toNat ≤ maximum := by
  have below := clears source
  rw [execution] at below
  exact below.bound address maximum bounded

end InitECandidate.Solver.GuestWork.MemzeroMemory
#print axioms InitECandidate.Solver.GuestWork.MemzeroMemory.clears
#print axioms InitECandidate.Solver.GuestWork.MemzeroMemory.saved_length
