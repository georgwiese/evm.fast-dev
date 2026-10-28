import InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost
import InitECandidate.Solver.Input.CurrentHash.StraightCost
import InitECandidate.Solver.Input.ClockCostScopeLocals

namespace InitECandidate.Solver.Input.CurrentHash.MerkleAllocationCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open MerkleBufferCost (afterZero afterMark afterSize afterBuffer)

def sizeExpression : ExpHOL 64 := .shift .lsl (.const 1#64) (localVar "dn")
def amountExpression : ExpHOL 64 := .panop .mul [localVar "size", .const 32#64]

set_option maxRecDepth 100000 in
theorem source_shape : afterZero = .decCall (ofString "mark") .one (Code.name .heap_mark) [] afterMark ∧
    afterMark = .dec (ofString "size") .one sizeExpression afterSize ∧
    afterSize = .decCall (ofString "buf") .one (ofString "alloc") [amountExpression] afterBuffer := by
  simp only [MerkleBufferCost.afterZero, MerkleBufferCost.afterMark, MerkleBufferCost.afterSize, MerkleBufferCost.afterBuffer,
    Merkle.afterDepth, Merkle.afterCount, Merkle.afterLimit, Merkle.body, Code.name,
    Guest.Software.guestFn_merkleize, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, sizeExpression, amountExpression, localVar]
  exact ⟨True.intro, True.intro, True.intro⟩

structure Params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n depth target : Nat) : Prop where
  pointer : source.locals.lookup (ofString "p") = some (.val (.word p))
  count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))
  dn : source.locals.lookup (ofString "dn") = some (.val (.word (BitVec.ofNat 64 depth)))
  maximum : source.locals.lookup (ofString "target") = some (.val (.word (BitVec.ofNat 64 target)))

theorem size_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (depth : Nat) (small : depth < 64)
    (dn : source.locals.lookup (ofString "dn") = some (.val (.word (BitVec.ofNat 64 depth)))) :
    eval source sizeExpression = some (.val (.word (BitVec.ofNat 64 (2^depth)))) := by
  have number : (BitVec.ofNat 64 depth).toNat = depth := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have shifted : ((1#64 : BitVec 64) <<< depth) = BitVec.ofNat 64 (2^depth) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have valid : ¬ (depth ≠ 0 ∧ 64 ≤ depth) := by omega
  simp [eval, sizeExpression, localVar, evalHOLExact, toExact, dn, wordShiftHOL, number, valid, shifted]

/-- An allocator failure is paid immediately. Only an actual checked scalar
return selects the buffer suffix, reinstalling the original caller locals. -/
theorem allocation_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n depth target : Nat)
    (data : Params source p n depth target) (installed : OriginalCode.Installed source.code)
    (size : source.locals.lookup (ofString "size") = some (.val (.word (BitVec.ofNat 64 (2^depth)))))
    (inside : n ≤ 2^depth) (small : 32*2^depth + 32 < 2^64) (targetSmall : target < 2^63) (depths : depth ≤ target) :
    source.clock - (evaluateHOLFiniteState source afterSize).2.clock ≤ 44*2^depth + 2*(target-depth) + 44 := by
  rw [source_shape.2.2]
  have priced := ClockCost.scalar_scope_current source "buf" (ofString "alloc") [amountExpression]
    PersistentAlloc.formals PersistentAlloc.body afterBuffer .one 1 (44*2^depth + 2*(target-depth) + 42)
    (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed) (by
      intro post buffer codeEq
      let entry := CallNormal.continuationEntry source post "buf" (.val (.word buffer))
      have kept (name : String) (different : ofString "buf" ≠ ofString name) :
          entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
        exact bind_lookup_other {post with locals := source.locals} "buf" name buffer different
      have fields : MerkleBufferCost.Locals entry p buffer n (2^depth) depth target :=
        ⟨(kept "p" (by decide)).trans data.pointer, bind_lookup_same _ _ _, (kept "n" (by decide)).trans data.count,
          (kept "size" (by decide)).trans size, (kept "dn" (by decide)).trans data.dn, (kept "target" (by decide)).trans data.maximum⟩
      have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed post.code; rw [codeEq]; exact installed
      exact MerkleBufferCost.cost entry p buffer n (2^depth) depth target fields currentCode (Nat.two_pow_pos depth) inside small targetSmall depths)
  omega

theorem sized_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n depth target : Nat)
    (data : Params source p n depth target) (installed : OriginalCode.Installed source.code)
    (depthSmall : depth < 64) (inside : n ≤ 2^depth) (small : 32*2^depth + 32 < 2^64)
    (targetSmall : target < 2^63) (depths : depth ≤ target) :
    source.clock - (evaluateHOLFiniteState source afterMark).2.clock ≤ 44*2^depth + 2*(target-depth) + 44 := by
  rw [source_shape.2.1]
  apply ClockCost.declared_current source "size" sizeExpression (BitVec.ofNat 64 (2^depth)) afterSize _ (size_read source depth depthSmall data.dn)
  let entry := bind source "size" (BitVec.ofNat 64 (2^depth))
  have next : Params entry p n depth target :=
    ⟨(bind_lookup_other source "size" "p" _ (by decide)).trans data.pointer,
      (bind_lookup_other source "size" "n" _ (by decide)).trans data.count,
      (bind_lookup_other source "size" "dn" _ (by decide)).trans data.dn,
      (bind_lookup_other source "size" "target" _ (by decide)).trans data.maximum⟩
  exact allocation_cost entry p n depth target next installed (bind_lookup_same _ _ _) inside small targetSmall depths

/-- Entire real nonempty allocation/fill/hash/release phase on every outcome.
No heap pointer, allocator room, mapped buffer or future return is a premise. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n depth target : Nat)
    (data : Params source p n depth target) (installed : OriginalCode.Installed source.code)
    (depthSmall : depth < 64) (inside : n ≤ 2^depth) (small : 32*2^depth + 32 < 2^64)
    (targetSmall : target < 2^63) (depths : depth ≤ target) :
    source.clock - (evaluateHOLFiniteState source afterZero).2.clock ≤ 44*2^depth + 2*(target-depth) + 45 := by
  rw [source_shape.1]
  have priced := ClockCost.scalar_scope_current source "mark" (Code.name .heap_mark) []
    (Code.formals .heap_mark) (Code.body .heap_mark) afterMark (Code.shape .heap_mark) 0 (44*2^depth + 2*(target-depth) + 44)
    (Code.installed source.code installed .heap_mark)
    (StraightCost.body source.code .heap_mark (StraightCost.basic_supported .heap_mark (by simp))) (by
      intro post mark codeEq
      let entry := CallNormal.continuationEntry source post "mark" (.val (.word mark))
      have kept (name : String) (different : ofString "mark" ≠ ofString name) :
          entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
        bind_lookup_other {post with locals := source.locals} "mark" name mark different
      have next : Params entry p n depth target :=
        ⟨(kept "p" (by decide)).trans data.pointer, (kept "n" (by decide)).trans data.count,
          (kept "dn" (by decide)).trans data.dn, (kept "target" (by decide)).trans data.maximum⟩
      have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed post.code; rw [codeEq]; exact installed
      exact sized_cost entry p n depth target next currentCode depthSmall inside small targetSmall depths)
  omega

end InitECandidate.Solver.Input.CurrentHash.MerkleAllocationCost

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleAllocationCost.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleAllocationCost.size_read
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleAllocationCost.allocation_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleAllocationCost.sized_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleAllocationCost.cost
