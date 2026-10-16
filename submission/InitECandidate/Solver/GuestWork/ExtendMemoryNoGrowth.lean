import InitECandidate.Solver.GuestWork.ExtendMemoryLength
import InitECandidate.Solver.FlattenWeighted.BlockSelected

namespace InitECandidate.Solver.GuestWork.ExtendMemoryNoGrowth
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
open ExtendMemoryLength (lengthReady)

/-- The actual capacity comparison is false, and the logical extension is
bounded. No validity assumption on subsequent memory loads/stores is needed. -/
def ready {C F : Type} (maximum : Nat) (state : StackSemStateFiniteExact 64 C F) : Prop :=
  lengthReady maximum state ∧ ∃ capacity nextLength,
    state.regs.lookup 12 = some (.word capacity) ∧
    state.regs.lookup 10 = some (.word nextLength) ∧ ¬ capacity < nextLength

theorem selected {C F : Type} (maximum : Nat) (state : StackSemStateFiniteExact 64 C F)
    (valid : ready maximum state) : branchChoice .lower 12 (.reg 10) state = some false := by
  obtain ⟨_, capacity, nextLength, hcapacity, hlength, noGrowth⟩ := valid
  simp [branchChoice, StackSemStateOps.getVar, StackSemStateOps.getVarImm,
    HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL, hcapacity, hlength, noGrowth]

private theorem save_bound {C F : Type} (maximum : Nat) :
    BlockBound (C := C) (F := F) NamedBody484_263 (ready maximum) (lengthReady maximum) 6 1 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro source post valid run
  have frame := normalFrame NamedBody484_263 11 (by decide) source post run
  obtain ⟨⟨installed, length, found, small⟩, _⟩ := valid
  refine ⟨?_, length, frame.1.trans found, small⟩
  rw [frame.2]
  exact installed

/-- The real capacity branch, including its comparison and return-slot saves. -/
theorem branch_bound {C F : Type} (maximum : Nat) :
    BlockBound (C := C) (F := F) NamedBody484_264 (ready maximum) (lengthReady maximum) 7 1 :=
  BlockBound.iteSelected .lower 12 (.reg 10) false (selected maximum) (save_bound maximum)

/-- The entire actual suffix from the capacity comparison through the final
memzero and EV_MEM_LEN store, when existing capacity already suffices. -/
theorem suffix_bound {C F : Type} (maximum : Nat) (maximumBound : maximum + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody484_364 (ready maximum) (fun _ => True)
      (17 * maximum + 534) (maximum + 47) := by
  have combined := (branch_bound (C := C) (F := F) maximum).seq
    (ExtendMemoryLength.length_suffix_bound maximum maximumBound)
  apply combined.weaken (fun _ h => h) (fun _ h => h) <;> omega

theorem bounded_suffix {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (maximum : Nat) (maximumBound : maximum + 32 < 2 ^ 64)
    (valid : ready maximum source)
    (execution : evaluate (NamedBody484_364, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (NamedBody484_364, {source with clock := maximum + 48}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work NamedBody484_364 {source with clock := maximum + 48} (17 * maximum + 534) :=
  (suffix_bound maximum maximumBound).boundedExecution (fun _ _ h => h)
    source post result valid execution notTimeout

end InitECandidate.Solver.GuestWork.ExtendMemoryNoGrowth
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryNoGrowth.selected
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryNoGrowth.branch_bound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryNoGrowth.suffix_bound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryNoGrowth.bounded_suffix
