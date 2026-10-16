import InitECandidate.Solver.GuestWork.MemzeroBytesRank
import InitECandidate.Solver.GuestWork.MemzeroTailRank
import InitECandidate.Solver.FlattenWeighted.BlockBound
import InitECandidate.Solver.FlattenWeighted.LoopTimeout

namespace InitECandidate.Solver.GuestWork.MemzeroSuffix
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound

def smallInvariant {C F : Type} (base length : BitVec 64)
    (state : StackSemStateFiniteExact 64 C F) : Prop :=
  ∃ index : BitVec 64,
    state.regs.lookup 10 = some (.word base) ∧
    state.regs.lookup 11 = some (.word length) ∧
    state.regs.lookup 12 = some (.word index) ∧
    index.toNat ≤ length.toNat ∧ length.toNat - index.toNat < 8

theorem byteLoopBound {C F : Type} (base length : BitVec 64)
    (bounded : length.toNat + 8 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody78_203
      (MemzeroBytes.invariant base length) (smallInvariant base length)
      ((length.toNat / 8 + 1) * 85) ((length.toNat / 8 + 1) * 3) := by
  constructor
  · intro state valid
    obtain ⟨index, hbase, hlength, hindex, indexBound⟩ := valid
    apply Work.mono (derivation := MemzeroBytes.loop_work state base length index bounded hbase hlength hindex indexBound)
    omega
  · intro state valid
    obtain ⟨index, hbase, hlength, hindex, indexBound⟩ := valid
    have consumed := MemzeroBytes.loop_clock state base length index bounded hbase hlength hindex indexBound
    change state.clock ≤ (evaluate (.loop MemzeroBytes.body, state)).2.clock + _
    omega
  · intro state next valid run
    exact MemzeroBytes.loop_exit base length bounded state next valid run
  · intro state next _ run
    have zero := loopTimeoutClock MemzeroBytes.body
      (fun state => basicTimeoutClock MemzeroBytes.body state MemzeroBytes.body_basic) state
    change evaluate (.loop MemzeroBytes.body, state) = _ at run
    rw [run] at zero
    exact zero rfl

theorem tailLoopBound {C F : Type} (base length : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody78_234
      (smallInvariant base length) (fun _ => True) 232 24 := by
  constructor
  · intro state valid
    obtain ⟨index, hbase, hlength, hindex, _, small⟩ := valid
    apply Work.mono (derivation := MemzeroTail.loop_work state base length index hbase hlength hindex)
    omega
  · intro state valid
    obtain ⟨index, hbase, hlength, hindex, _, small⟩ := valid
    have consumed := MemzeroTail.loop_clock state base length index hbase hlength hindex
    change state.clock ≤ (evaluate (.loop MemzeroTail.body, state)).2.clock + _
    omega
  · intro _ _ _ _
    trivial
  · intro state next _ run
    have zero := loopTimeoutClock MemzeroTail.body
      (fun state => basicTimeoutClock MemzeroTail.body state MemzeroTail.body_basic) state
    change evaluate (.loop MemzeroTail.body, state) = _ at run
    rw [run] at zero
    exact zero rfl

theorem skipBound {C F : Type} (pre : StackSemStateFiniteExact 64 C F → Prop) :
    BlockBound .skip pre pre 1 0 := by
  apply BlockBound.basic .skip pre pre (by decide)
  intro state next valid run
  rw [evaluate_skip] at run
  have same : state = next := congrArg Prod.snd run
  simpa only [same] using valid

theorem tickBound {C F : Type} (pre : StackSemStateFiniteExact 64 C F → Prop)
    (stable : ∀ state, pre state → pre (decClock state)) : BlockBound .tick pre pre 2 1 := by
  apply BlockBound.basic .tick pre pre (by decide)
  intro state next valid run
  rw [evaluate_tick] at run
  split at run
  · simp at run
  · have same : decClock state = next := congrArg Prod.snd run
    simpa only [same] using stable state valid

private theorem returnBound {C F : Type} :
    BlockBound (C := C) (F := F) NamedBody78_241 (fun _ => True) (fun _ => True) 8 1 := by
  have supported : basic NamedBody78_241 = true := by decide
  have nodeCount : nodes NamedBody78_241 = 7 := by decide
  have tickCount : ticks NamedBody78_241 = 1 := by decide
  simpa only [nodeCount, tickCount] using
    BlockBound.basic NamedBody78_241 (fun _ => True) (fun _ => True) supported (by intros; trivial)

theorem tailSuffixBound {C F : Type} (base length : BitVec 64) :
    BlockBound (C := C) (F := F) NamedBody78_245
      (smallInvariant base length) (fun _ => True) 245 27 := by
  have tick := tickBound (C := C) (F := F) (smallInvariant base length) (fun _ valid => valid)
  exact tick.seq (tick.seq ((skipBound _).seq ((tailLoopBound base length).seq returnBound)))

/-- The actual unaligned eight-byte loop, final byte loop and return compose
under the in-range index invariant. The byte-tail cost is at most 232 credits,
independent of total length, because the preceding loop leaves fewer than eight. -/
theorem suffixBound {C F : Type} (base length : BitVec 64)
    (bounded : length.toNat + 8 < 2 ^ 64) :
    BlockBound (C := C) (F := F) NamedBody78_246
      (MemzeroBytes.invariant base length) (fun _ => True)
      ((length.toNat / 8 + 1) * 85 + 245) ((length.toNat / 8 + 1) * 3 + 27) :=
  (byteLoopBound base length bounded).seq (tailSuffixBound base length)

end InitECandidate.Solver.GuestWork.MemzeroSuffix
#print axioms InitECandidate.Solver.GuestWork.MemzeroSuffix.byteLoopBound
#print axioms InitECandidate.Solver.GuestWork.MemzeroSuffix.tailLoopBound
#print axioms InitECandidate.Solver.GuestWork.MemzeroSuffix.tailSuffixBound
#print axioms InitECandidate.Solver.GuestWork.MemzeroSuffix.suffixBound
