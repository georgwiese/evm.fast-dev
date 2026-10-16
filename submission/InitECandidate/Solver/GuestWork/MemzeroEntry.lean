import InitECandidate.Solver.GuestWork.MemzeroAligned
import InitECandidate.Solver.FlattenWeighted.BlockReclock

namespace InitECandidate.Solver.GuestWork.MemzeroEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted
open MemzeroAligned (quadCount wordCount)

def pre {C F : Type} (base length : BitVec 64) (state : StackSemStateFiniteExact 64 C F) : Prop :=
  state.regs.lookup 10 = some (.word base) ∧ state.regs.lookup 11 = some (.word length)

private theorem initIndexBound {C F : Type} (base length : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody78_2 (pre base length)
      (MemzeroBytes.invariant base length) 1 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro state next valid run
  obtain ⟨hb, hl⟩ := valid
  simp [NamedBody78_2, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp, setVar] at run
  subst next
  refine ⟨0#64, ?_, ?_, ?_, ?_⟩
  all_goals simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hb, hl]

private theorem maskBound {C F : Type} (base length : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody78_4 (MemzeroBytes.invariant base length)
      (MemzeroBytes.invariant base length) 1 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro state next valid run
  obtain ⟨index, hb, hl, hi, ir⟩ := valid
  simp [NamedBody78_4, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, setVar, hb] at run
  subst next
  refine ⟨index, ?_, ?_, ?_, ir⟩
  all_goals simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hb, hl, hi]

private theorem zeroBound {C F : Type} (base length : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody78_5 (MemzeroBytes.invariant base length)
      (MemzeroBytes.invariant base length) 1 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro state next valid run
  obtain ⟨index, hb, hl, hi, ir⟩ := valid
  simp [NamedBody78_5, evaluate_inst, StackSemInst.instHOL, instInteger, assign, wordExp, setVar] at run
  subst next
  refine ⟨index, ?_, ?_, ?_, ir⟩
  all_goals simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hb, hl, hi]

def workBudget (length : BitVec 64) : Nat := quadCount length * 61 + wordCount length * 116 + 270
def consumedBudget (length : BitVec 64) : Nat := quadCount length * 3 + wordCount length * 6 + 34

/-- Full fixed Named78 procedure: initialization, optional aligned loops,
unaligned byte loop, short byte tail, and return. The length premise prevents
wrapping in every block guard; no assumption about successful stores is added. -/
theorem entryBound {C F : Type} (base length : BitVec 64)
    (bounded : length.toNat + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) Named78.2 (pre base length) (fun _ => True)
      (workBudget length) (consumedBudget length) := by
  have tick := MemzeroSuffix.tickBound (C := C) (F := F) (MemzeroBytes.invariant base length)
    (fun _ valid => valid)
  have skip := MemzeroSuffix.skipBound (C := C) (F := F) (MemzeroBytes.invariant base length)
  have firstSkip := MemzeroSuffix.skipBound (C := C) (F := F) (pre base length)
  have suffix := MemzeroSuffix.suffixBound (C := C) (F := F) base length (by omega)
  have branch := MemzeroAligned.branchBound (C := C) (F := F) base length bounded
  have rest := branch.seq (tick.seq (tick.seq (skip.seq suffix)))
  have all := firstSkip.seq (firstSkip.seq ((initIndexBound base length).seq
    (skip.seq ((maskBound base length).seq ((zeroBound base length).seq rest)))))
  apply all.weaken (fun _ h => h) (fun _ h => h)
  · dsimp only [workBudget, MemzeroAligned.alignedCredits, quadCount, wordCount]
    omega
  · dsimp only [consumedBudget, MemzeroAligned.alignedClocks, quadCount, wordCount]
    omega

/-- Any non-timeout run of the actual complete memzero procedure has an
execution with explicit bounded initial clock and the same result/full final
state apart from unused clock, with its source work budget available. -/
theorem bounded_execution {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (base length : BitVec 64) (bounded : length.toNat + 32 < 2 ^ 64)
    (hbase : source.regs.lookup 10 = some (.word base))
    (hlength : source.regs.lookup 11 = some (.word length))
    (execution : evaluate (Named78.2, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (Named78.2, {source with clock := consumedBudget length + 1}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work Named78.2 {source with clock := consumedBudget length + 1} (workBudget length) :=
  (entryBound base length bounded).boundedExecution (fun _ _ h => h)
    source post result ⟨hbase, hlength⟩ execution notTimeout

end InitECandidate.Solver.GuestWork.MemzeroEntry
#print axioms InitECandidate.Solver.GuestWork.MemzeroEntry.entryBound
#print axioms InitECandidate.Solver.GuestWork.MemzeroEntry.bounded_execution
