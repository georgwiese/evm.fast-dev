import InitECandidate.Solver.Input.CurrentHash.PackBytesArguments
import InitECandidate.Solver.Input.CurrentHash.MemoryCost
import InitECandidate.Solver.Input.CurrentHash.AllocatorCost
import InitECandidate.Solver.Input.ClockCostScopeLocals
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentHash.PackBytesCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def price (n : Nat) := CopyAny.price n + ZeroAny.price (PackBytes.padded n - n) + 4

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n : Nat) : Prop where
  pointer : source.locals.lookup (ofString "p") = some (.val (.word p))
  buf : source.locals.lookup (ofString "buf") = some (.val (.word buffer))
  length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))
  count : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 (PackBytes.chunks n))))

theorem Locals.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {p buffer : BitVec 64} {n : Nat}
    (data : Locals source p buffer n) (function : MlS) (arguments : List (ExpHOL 64))
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (none, post)) : Locals post p buffer n := by
  have kept (name : MlS) : post.locals.lookup name = source.locals.lookup name := CallNormal.ignored_lookup source post name function arguments actual
  exact ⟨(kept _).trans data.pointer, (kept _).trans data.buf, (kept _).trans data.length, (kept _).trans data.count⟩

theorem copy_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n : Nat)
    (data : Locals source p buffer n) (installed : OriginalCode.Installed source.code) (small : n + 64 < 2^64) :
    source.clock - (evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memcpy") PackBytes.copyArguments)).2.clock ≤ CopyAny.price n + 1 := by
  apply MemoryCost.copy source installed (some none) PackBytes.copyArguments buffer p n (by omega)
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, PackBytes.copyArguments, localVar,
    data.buf, data.pointer, data.length, CopyGeneral.values]

theorem zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n : Nat)
    (data : Locals source p buffer n) (installed : OriginalCode.Installed source.code) (small : n + 64 < 2^64) :
    source.clock - (evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memzero") PackBytes.zeroArguments)).2.clock ≤ ZeroAny.price (PackBytes.padded n - n) + 1 := by
  apply MemoryCost.zero source installed (some none) PackBytes.zeroArguments (buffer + BitVec.ofNat 64 n) (PackBytes.padded n - n)
    (by have bounds := PackBytes.padding_bounds n; omega)
  exact PackBytesArguments.zero_arguments source buffer n small data.buf data.length data.count

theorem buffer_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n : Nat)
    (data : Locals source p buffer n) (installed : OriginalCode.Installed source.code) (small : n + 64 < 2^64) :
    source.clock - (evaluateHOLFiniteState source PackBytes.afterBuffer).2.clock ≤ CopyAny.price n + 1 + (ZeroAny.price (PackBytes.padded n - n) + 1) := by
  rw [PackBytes.body_shape.2.2.1]
  apply ClockCost.sequence_reached_current source _ PackBytes.afterCopy _ _ (copy_cost source p buffer n data installed small)
  intro post copied
  have next := data.after_call _ _ copied
  have currentCode : OriginalCode.Installed post.code := by rw [(evaluation_fields source post _ none copied).2.2.2]; exact installed
  rw [PackBytes.body_shape.2.2.2]
  exact ClockCost.sequence_current post _ _ _ 0 (zero_cost post p buffer n next currentCode small) (ClockCost.returned post.code _)

/-- Real persistent allocation plus exact byte copy/padding. Failure paths are
included, and the suffix is priced only after a checked actual scalar return. -/
theorem allocation_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n : Nat)
    (installed : OriginalCode.Installed source.code) (small : n + 64 < 2^64)
    (pointer : source.locals.lookup (ofString "p") = some (.val (.word p)))
    (length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (count : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 (PackBytes.chunks n))))) :
    source.clock - (evaluateHOLFiniteState source PackBytes.afterCount).2.clock ≤ price n := by
  rw [PackBytes.body_shape.2.1]
  have priced := ClockCost.scalar_scope_current source "buf" (ofString "alloc") [PackBytes.amountExpression]
    PersistentAlloc.formals PersistentAlloc.body PackBytes.afterBuffer .one 1
    (CopyAny.price n + 1 + (ZeroAny.price (PackBytes.padded n - n) + 1))
    (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed) (by
      intro post buffer codeEq
      let entry := CallNormal.continuationEntry source post "buf" (.val (.word buffer))
      have kept (name : String) (different : ofString "buf" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
        bind_lookup_other {post with locals := source.locals} "buf" name buffer different
      have fields : Locals entry p buffer n := ⟨(kept "p" (by decide)).trans pointer, bind_lookup_same _ _ _,
        (kept "n" (by decide)).trans length, (kept "count" (by decide)).trans count⟩
      have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed post.code; rw [codeEq]; exact installed
      exact buffer_cost entry p buffer n fields currentCode small)
  unfold price
  omega

/-- Whole actual pack_bytes source-clock cost on every outcome. Length bounds
are actual current arguments; there is no allocation-room/mapping/success or
minimum-clock premise. Padding is charged at its actual≤31byte length. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n : Nat)
    (installed : OriginalCode.Installed source.code) (small : n + 64 < 2^64)
    (pointer : source.locals.lookup (ofString "p") = some (.val (.word p)))
    (length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))) :
    source.clock - (evaluateHOLFiniteState source PackBytes.body).2.clock ≤ price n := by
  rw [PackBytes.body_shape.1]
  apply ClockCost.declared_current source "count" PackBytes.countExpression (BitVec.ofNat 64 (PackBytes.chunks n)) PackBytes.afterCount _
    (PackBytes.count_read_bounded source n (by omega) length)
  exact allocation_cost (bind source "count" (BitVec.ofNat 64 (PackBytes.chunks n))) p n installed small
    ((bind_lookup_other source "count" "p" _ (by decide)).trans pointer)
    ((bind_lookup_other source "count" "n" _ (by decide)).trans length) (bind_lookup_same _ _ _)

theorem price_bound (n : Nat) : price n ≤ CopyAny.price n + 41 := by
  have bounds := PackBytes.padding_bounds n
  unfold price ZeroAny.price
  omega

end InitECandidate.Solver.Input.CurrentHash.PackBytesCost

#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCost.Locals.after_call
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCost.copy_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCost.zero_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCost.buffer_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCost.allocation_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCost.cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesCost.price_bound
