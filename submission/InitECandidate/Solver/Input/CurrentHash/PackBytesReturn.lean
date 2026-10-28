import InitECandidate.Solver.Input.CurrentHash.PackBytesCost
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.NormalCallEntry
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Input.CurrentHash.PackBytesReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def tuple (pointer : BitVec 64) (n : Nat) : ValueHOL 64 :=
  .rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 (PackBytes.chunks n)))]

/-- Actual normal copy/zero calls retain the real buffer/count locals until
literal tuple return. No successful memory operation is supplied separately. -/
theorem buffer_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n : Nat)
    (data : PackBytesCost.Locals source p buffer n) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source PackBytes.afterBuffer = (some (.returned value), post)) : value = tuple buffer n := by
  have copySafe : LocalPrefix (ofString "buf") (.call (some (none, none)) (ofString "memcpy") PackBytes.copyArguments) :=
    .call none _ _ (by intro name impossible; cases impossible)
  rw [PackBytes.body_shape.2.2.1] at actual
  obtain ⟨copied, copyRun, remaining⟩ := Input.sequence_returned source post _ _ value (copySafe.summary_full source).2.1 actual
  have copiedData := data.after_call _ _ copyRun
  have zeroSafe : LocalPrefix (ofString "buf") (.call (some (none, none)) (ofString "memzero") PackBytes.zeroArguments) :=
    .call none _ _ (by intro name impossible; cases impossible)
  rw [PackBytes.body_shape.2.2.2] at remaining
  obtain ⟨cleared, zeroRun, finished⟩ := Input.sequence_returned copied post _ _ value (zeroSafe.summary_full copied).2.1 remaining
  have finalData := copiedData.after_call _ _ zeroRun
  have returned : evaluateHOLFiniteState cleared (.return (.rstruct [localVar "buf", localVar "count"])) =
      (some (.returned (tuple buffer n)), emptyLocalsHOLFinite cleared) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, localVar,
      finalData.buf, finalData.count, tuple, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [returned] at finished
  exact (PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst finished))).symm

/-- A genuine whole pack_bytes return has its actual scalar allocation result
and the exact ceil(n/32) chunk count. This inverts the same real body run. -/
theorem body_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n : Nat)
    (small : n + 31 < 2^64)
    (pointer : source.locals.lookup (ofString "p") = some (.val (.word p)))
    (length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source PackBytes.body = (some (.returned value), post)) :
    ∃ buffer : BitVec 64, value = tuple buffer n := by
  rw [PackBytes.body_shape.1] at actual
  obtain ⟨declaredPost, declarationRun, declarationEndpoint⟩ := declaration_return_word source post "count" PackBytes.countExpression
    (BitVec.ofNat 64 (PackBytes.chunks n)) PackBytes.afterCount value (PackBytes.count_read_bounded source n small length) actual
  let declared := bind source "count" (BitVec.ofNat 64 (PackBytes.chunks n))
  change evaluateHOLFiniteState declared PackBytes.afterCount = (some (.returned value), declaredPost) at declarationRun
  rw [PackBytes.body_shape.2.1] at declarationRun
  obtain ⟨allocated, returnedBuffer, inner, remaining, endpoint, domain, endian, shapes, code, typed⟩ :=
    CallNormal.normal_entry declared declaredPost "buf" .one (ofString "alloc") [PackBytes.amountExpression] PackBytes.afterBuffer value declarationRun
  have scalar : shapeOfHOLExact returnedBuffer = .one := (shapeEqHOL_eq_true _ _).mp typed
  obtain ⟨buffer, rfl⟩ := ScalarShape.word returnedBuffer scalar
  let entry := CallNormal.continuationEntry declared allocated "buf" (.val (.word buffer))
  have kept (name : String) (different : ofString "buf" ≠ ofString name) : entry.locals.lookup (ofString name) = declared.locals.lookup (ofString name) :=
    bind_lookup_other {allocated with locals := declared.locals} "buf" name buffer different
  have data : PackBytesCost.Locals entry p buffer n :=
    ⟨(kept "p" (by decide)).trans ((bind_lookup_other source "count" "p" _ (by decide)).trans pointer), bind_lookup_same _ _ _,
      (kept "n" (by decide)).trans ((bind_lookup_other source "count" "n" _ (by decide)).trans length),
      (kept "count" (by decide)).trans (bind_lookup_same _ _ _)⟩
  exact ⟨buffer, buffer_return entry inner p buffer n data value remaining⟩

end InitECandidate.Solver.Input.CurrentHash.PackBytesReturn

#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesReturn.buffer_return
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesReturn.body_return
