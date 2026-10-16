import InitECandidate.Solver.GuestWork.MemzeroQuadRank
import InitECandidate.Solver.GuestWork.MemzeroWordRank
import InitECandidate.Solver.GuestWork.MemzeroSuffix
import InitECandidate.Solver.FlattenWeighted.BlockIf

namespace InitECandidate.Solver.GuestWork.MemzeroAligned
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted

abbrev invariant {C F : Type} := @MemzeroBytes.invariant C F

def quadCount (length : BitVec 64) : Nat := length.toNat / 32 + 1
def wordCount (length : BitVec 64) : Nat := length.toNat / 8 + 1

theorem quadLoopBound {C F : Type} (base length : BitVec 64)
    (bounded : length.toNat + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody78_68 (invariant base length) (invariant base length)
      (quadCount length * 61) (quadCount length * 3) := by
  constructor
  · intro state valid
    obtain ⟨index, hbase, hlength, hindex, indexBound⟩ := valid
    apply Work.mono (derivation := MemzeroQuad.loop_work state base length index bounded hbase hlength hindex indexBound)
    dsimp only [quadCount]
    omega
  · intro state valid
    obtain ⟨index, hbase, hlength, hindex, indexBound⟩ := valid
    have consumed := MemzeroQuad.loop_clock state base length index bounded hbase hlength hindex indexBound
    change state.clock ≤ (evaluate (.loop MemzeroQuad.body, state)).2.clock + _
    dsimp only [quadCount]
    omega
  · intro state next valid run
    obtain ⟨index, hb, hl, hi, ir, _⟩ := MemzeroQuad.loop_exit base length bounded state next valid run
    exact ⟨index, hb, hl, hi, ir⟩
  · intro state next _ run
    have zero := loopTimeoutClock MemzeroQuad.body
      (fun state => basicTimeoutClock MemzeroQuad.body state MemzeroQuad.body_basic) state
    change evaluate (.loop MemzeroQuad.body, state) = _ at run
    rw [run] at zero
    exact zero rfl

theorem wordLoopBound {C F : Type} (base length : BitVec 64)
    (bounded : length.toNat + 8 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody78_101 (invariant base length) (invariant base length)
      (wordCount length * 31) (wordCount length * 3) := by
  constructor
  · intro state valid
    obtain ⟨index, hbase, hlength, hindex, indexBound⟩ := valid
    apply Work.mono (derivation := MemzeroWord.loop_work state base length index bounded hbase hlength hindex indexBound)
    dsimp only [wordCount]
    omega
  · intro state valid
    obtain ⟨index, hbase, hlength, hindex, indexBound⟩ := valid
    have consumed := MemzeroWord.loop_clock state base length index bounded hbase hlength hindex indexBound
    change state.clock ≤ (evaluate (.loop MemzeroWord.body, state)).2.clock + _
    dsimp only [wordCount]
    omega
  · intro state next valid run
    obtain ⟨index, hb, hl, hi, ir, _⟩ := MemzeroWord.loop_exit base length bounded state next valid run
    exact ⟨index, hb, hl, hi, ir⟩
  · intro state next _ run
    have zero := loopTimeoutClock MemzeroWord.body
      (fun state => basicTimeoutClock MemzeroWord.body state MemzeroWord.body_basic) state
    change evaluate (.loop MemzeroWord.body, state) = _ at run
    rw [run] at zero
    exact zero rfl

def alignedCredits (length : BitVec 64) : Nat := quadCount length * 61 + wordCount length * 31 + 13
def alignedClocks (length : BitVec 64) : Nat := quadCount length * 3 + wordCount length * 3 + 5

theorem alignedBound {C F : Type} (base length : BitVec 64)
    (bounded : length.toNat + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody78_112 (invariant base length) (invariant base length)
      (alignedCredits length) (alignedClocks length) := by
  have tick := MemzeroSuffix.tickBound (C := C) (F := F) (invariant base length) (fun _ valid => valid)
  have skip := MemzeroSuffix.skipBound (C := C) (F := F) (invariant base length)
  have quad := quadLoopBound (C := C) (F := F) base length bounded
  have word := wordLoopBound (C := C) (F := F) base length (by omega)
  have chain := tick.seq (tick.seq (skip.seq (quad.seq
    (tick.seq (tick.seq (skip.seq (word.seq (tick.seq skip))))))))
  apply chain.weaken (fun _ h => h) (fun _ h => h)
  · dsimp only [alignedCredits]
    omega
  · dsimp only [alignedClocks]
    omega

theorem branchBound {C F : Type} (base length : BitVec 64)
    (bounded : length.toNat + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody78_116 (invariant base length) (invariant base length)
      (alignedCredits length + 1) (alignedClocks length) := by
  have tick := MemzeroSuffix.tickBound (C := C) (F := F) (invariant base length) (fun _ valid => valid)
  have skip := MemzeroSuffix.skipBound (C := C) (F := F) (invariant base length)
  have short := tick.seq skip
  have short' : BlockBound (C := C) (F := F) NamedBody78_115 (invariant base length) (invariant base length)
      (alignedCredits length) (alignedClocks length) := by
    apply short.weaken (fun _ h => h) (fun _ h => h)
    · dsimp only [alignedCredits]
      omega
    · dsimp only [alignedClocks]
      omega
  exact BlockBound.ite .equal 13 (.reg 5) (alignedBound base length bounded) short'

end InitECandidate.Solver.GuestWork.MemzeroAligned
#print axioms InitECandidate.Solver.GuestWork.MemzeroAligned.quadLoopBound
#print axioms InitECandidate.Solver.GuestWork.MemzeroAligned.wordLoopBound
#print axioms InitECandidate.Solver.GuestWork.MemzeroAligned.alignedBound
#print axioms InitECandidate.Solver.GuestWork.MemzeroAligned.branchBound
