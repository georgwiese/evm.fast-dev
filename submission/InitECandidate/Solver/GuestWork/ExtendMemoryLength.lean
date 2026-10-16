import InitECandidate.Solver.GuestWork.ExtendMemoryCalls
import InitECandidate.Solver.GuestWork.ExtendMemoryTransfer

namespace InitECandidate.Solver.GuestWork.ExtendMemoryLength
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def lengthReady {C F : Type} (maximum : Nat) (state : StackSemStateFiniteExact 64 C F) : Prop :=
  sptLookup 78 state.code = some Named78.2 ∧
  ∃ length, state.regs.lookup 11 = some (.word length) ∧ length.toNat ≤ maximum

def callReady {C F : Type} (maximum : Nat) (state : StackSemStateFiniteExact 64 C F) : Prop :=
  sptLookup 78 state.code = some Named78.2 ∧
  ∃ base length, state.regs.lookup 10 = some (.word base) ∧
    state.regs.lookup 11 = some (.word length) ∧ length.toNat ≤ maximum

theorem after_capacity_ready {C F : Type} (state : StackSemStateFiniteExact 64 C F)
    (stack metadata : BitVec 64) (maximum : Nat)
    (valid : ExtendMemoryTransfer.afterCall stack metadata maximum state) : lengthReady maximum state :=
  ⟨valid.1, valid.2.2.2⟩

/-- Uniform version of the actual final call/store suffix. Its base address is
unrestricted; the word length and installed code supply the cost premises. -/
theorem call_suffix_bound {C F : Type} (maximum : Nat) (maximumBound : maximum + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody484_354 (callReady maximum) (fun _ => True)
      (17 * maximum + 517) (maximum + 45) := by
  constructor
  · intro source valid
    obtain ⟨installed, base, length, hbase, hlength, small⟩ := valid
    exact (ExtendMemoryCalls.suffixBound base length maximum small maximumBound).work source
      ⟨installed, hbase, hlength⟩
  · intro source valid
    obtain ⟨installed, base, length, hbase, hlength, small⟩ := valid
    exact (ExtendMemoryCalls.suffixBound base length maximum small maximumBound).clock source
      ⟨installed, hbase, hlength⟩
  · intro _ _ _ _
    trivial
  · intro source post valid run
    obtain ⟨installed, base, length, hbase, hlength, small⟩ := valid
    exact (ExtendMemoryCalls.suffixBound base length maximum small maximumBound).timeout source post
      ⟨installed, hbase, hlength⟩ run

private theorem preserve_length {C F : Type} (prog : HolProg 64) (maximum : Nat)
    (supported : basic prog = true) (safe : keepsReg 11 prog = true) :
    BlockBound (C := C) (F := F) prog (lengthReady maximum) (lengthReady maximum)
      (ticks prog + nodes prog) (ticks prog) := by
  apply BlockBound.basic _ _ _ supported
  intro source post valid run
  obtain ⟨installed, length, found, small⟩ := valid
  have frame := normalFrame prog 11 safe source post run
  refine ⟨?_, length, frame.1.trans found, small⟩
  rw [frame.2]
  exact installed

private theorem base_bound {C F : Type} (maximum : Nat) :
    BlockBound (C := C) (F := F) NamedBody484_272 (lengthReady maximum) (callReady maximum) 1 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro source post valid run
  obtain ⟨installed, length, found, small⟩ := valid
  have frame := normalFrame NamedBody484_272 11 (by decide) source post run
  cases value : wordExp source (.op .add [.var 5, .var 1]) with
  | none =>
    simp [NamedBody484_272, evaluate_inst, StackSemInst.instHOL, instInteger, assign, value] at run
  | some base =>
    simp [NamedBody484_272, evaluate_inst, StackSemInst.instHOL, instInteger, assign, value] at run
    subst post
    refine ⟨installed, base, length, ?_, ?_, small⟩
    · simp [setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · exact frame.1.trans found

private theorem call_skip {C F : Type} (maximum : Nat) :
    BlockBound (C := C) (F := F) NamedBody484_273 (callReady maximum) (callReady maximum) 1 0 := by
  apply BlockBound.basic _ _ _ (by decide)
  intro source post valid run
  simp only [NamedBody484_273, evaluate_skip, Prod.mk.injEq, true_and] at run
  subst post
  exact valid

/-- Entire actual logical-expansion suffix, including pointer lookup and
address computation. Invalid pointer data stops early; it is not assumed valid. -/
theorem length_suffix_bound {C F : Type} (maximum : Nat) (maximumBound : maximum + 32 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody484_363 (lengthReady maximum) (fun _ => True)
      (17 * maximum + 527) (maximum + 46) := by
  have final := (call_skip (C := C) (F := F) maximum).seq (call_suffix_bound maximum maximumBound)
  have withBase := (base_bound (C := C) (F := F) maximum).seq final
  have all := (preserve_length NamedBody484_265 maximum (by decide) (by decide)).seq
    ((preserve_length NamedBody484_266 maximum (by decide) (by decide)).seq
    ((preserve_length NamedBody484_267 maximum (by decide) (by decide)).seq
    ((preserve_length NamedBody484_268 maximum (by decide) (by decide)).seq
    ((preserve_length NamedBody484_269 maximum (by decide) (by decide)).seq
    ((preserve_length NamedBody484_270 maximum (by decide) (by decide)).seq
    ((preserve_length NamedBody484_271 maximum (by decide) (by decide)).seq withBase))))))
  apply all.weaken (fun _ h => h) (fun _ h => h) <;>
    simp [ticks, nodes, NamedBody484_265, NamedBody484_266, NamedBody484_267, NamedBody484_268,
      NamedBody484_269, NamedBody484_270, NamedBody484_271] <;> omega

theorem bounded_length_suffix {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (maximum : Nat) (maximumBound : maximum + 32 < 2 ^ 64)
    (valid : lengthReady maximum source)
    (execution : evaluate (NamedBody484_363, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    ∃ boundedPost,
      evaluate (NamedBody484_363, {source with clock := maximum + 47}) = (result, boundedPost) ∧
      {boundedPost with clock := 0} = {post with clock := 0} ∧
      Work NamedBody484_363 {source with clock := maximum + 47} (17 * maximum + 527) :=
  (length_suffix_bound maximum maximumBound).boundedExecution (fun _ _ h => h)
    source post result valid execution notTimeout

end InitECandidate.Solver.GuestWork.ExtendMemoryLength
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryLength.after_capacity_ready
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryLength.call_suffix_bound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryLength.length_suffix_bound
#print axioms InitECandidate.Solver.GuestWork.ExtendMemoryLength.bounded_length_suffix
