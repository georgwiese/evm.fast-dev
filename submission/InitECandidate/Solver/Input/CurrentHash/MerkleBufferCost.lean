import InitECandidate.Solver.Input.CurrentHash.MerkleSuffixCost
import InitECandidate.Solver.Input.MerkleProgram
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def afterZero : ProgHOL 64 := match Merkle.afterDepth with | .seq _ rest => rest | _ => .skip
def afterMark : ProgHOL 64 := match afterZero with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterSize : ProgHOL 64 := match afterMark with | .dec _ _ _ rest => rest | _ => .skip
def afterBuffer : ProgHOL 64 := match afterSize with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterCopy : ProgHOL 64 := match afterBuffer with | .seq _ rest => rest | _ => .skip
def afterClear : ProgHOL 64 := match afterCopy with | .seq _ rest => rest | _ => .skip

def copyArguments : List (ExpHOL 64) := [localVar "buf", localVar "p", .panop .mul [localVar "n", .const 32#64]]
def zeroArguments : List (ExpHOL 64) := [.op .add [localVar "buf", .panop .mul [localVar "n", .const 32#64]],
  .panop .mul [.op .sub [localVar "size", localVar "n"], .const 32#64]]

set_option maxRecDepth 100000 in
theorem source_shape : afterBuffer = .seq (.call (some (none, none)) (ofString "memcpy") copyArguments) afterCopy ∧
    afterCopy = .seq (.call (some (none, none)) (ofString "memzero") zeroArguments) afterClear ∧
    afterClear = .dec (ofString "cur") .one (localVar "size") MerkleSuffixCost.denseContinuation := by
  simp only [afterBuffer, afterSize, afterMark, afterZero, afterCopy, afterClear,
    Merkle.afterDepth, Merkle.afterCount, Merkle.afterLimit, Merkle.body,
    MerkleSuffixCost.denseContinuation, MerkleSuffixCost.loopSequences,
    Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_merkleize, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.append_nil, List.nil_append, List.cons_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Option.map_none,
    copyArguments, zeroArguments, localVar]
  exact ⟨True.intro, True.intro, True.intro⟩

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n capacity depth target : Nat) : Prop where
  pointer : source.locals.lookup (ofString "p") = some (.val (.word p))
  buf : source.locals.lookup (ofString "buf") = some (.val (.word buffer))
  count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))
  size : source.locals.lookup (ofString "size") = some (.val (.word (BitVec.ofNat 64 capacity)))
  dn : source.locals.lookup (ofString "dn") = some (.val (.word (BitVec.ofNat 64 depth)))
  maximum : source.locals.lookup (ofString "target") = some (.val (.word (BitVec.ofNat 64 target)))

theorem Locals.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {p buffer : BitVec 64} {n capacity depth target : Nat}
    (data : Locals source p buffer n capacity depth target) (function : MlS) (arguments : List (ExpHOL 64))
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (none, post)) :
    Locals post p buffer n capacity depth target := by
  have kept (name : MlS) : post.locals.lookup name = source.locals.lookup name := CallNormal.ignored_lookup source post name function arguments actual
  exact ⟨(kept _).trans data.pointer, (kept _).trans data.buf, (kept _).trans data.count,
    (kept _).trans data.size, (kept _).trans data.dn, (kept _).trans data.maximum⟩

theorem copy_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n capacity depth target : Nat)
    (data : Locals source p buffer n capacity depth target) (installed : OriginalCode.Installed source.code)
    (small : 32*n + 32 < 2^64) :
    source.clock - (evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memcpy") copyArguments)).2.clock ≤ CopyAny.price (32*n) + 1 := by
  apply MemoryCost.copy source installed (some none) copyArguments buffer p (32*n) small
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, copyArguments, localVar,
    data.buf, data.pointer, data.count, CopyGeneral.values, valueIsWord, valueWord, panOpHOL, BitVec.ofNat_mul, Nat.mul_comm]

theorem zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n capacity depth target : Nat)
    (data : Locals source p buffer n capacity depth target) (installed : OriginalCode.Installed source.code)
    (inside : n ≤ capacity) (small : 32*capacity + 32 < 2^64) :
    source.clock - (evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memzero") zeroArguments)).2.clock ≤ ZeroAny.price (32*(capacity-n)) + 1 := by
  have difference := BitVec.ofNat_sub_ofNat_of_le (w := 64) capacity n (by omega) inside
  apply MemoryCost.zero source installed (some none) zeroArguments (buffer + BitVec.ofNat 64 (32*n)) (32*(capacity-n)) (by omega)
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, zeroArguments, localVar,
    data.buf, data.count, data.size, Zero.values, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
    difference, BitVec.ofNat_mul, Nat.mul_comm]

theorem after_clear_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n capacity depth target : Nat)
    (data : Locals source p buffer n capacity depth target) (installed : OriginalCode.Installed source.code)
    (positive : 1 ≤ capacity) (small : capacity < 2^63) (targetSmall : target < 2^63) (depths : depth ≤ target) :
    source.clock - (evaluateHOLFiniteState source afterClear).2.clock ≤ 3*(capacity-1) + (2*(target-depth)+43) := by
  have read : eval source (localVar "size") = some (.val (.word (BitVec.ofNat 64 capacity))) := by
    simpa [eval, localVar, evalHOLExact, toExact] using data.size
  rw [source_shape.2.2]
  apply ClockCost.declared_current source "cur" (localVar "size") (BitVec.ofNat 64 capacity) MerkleSuffixCost.denseContinuation _ read
  exact MerkleSuffixCost.cost (bind source "cur" (BitVec.ofNat 64 capacity)) capacity capacity depth target positive (Nat.le_refl _) small targetSmall depths installed
    (bind_lookup_same _ _ _) ((bind_lookup_other source "cur" "dn" _ (by decide)).trans data.dn)
    ((bind_lookup_other source "cur" "target" _ (by decide)).trans data.maximum)

/-- Complete actual buffer copy/clear/dense/extension/output work, including
partial and failed executions. Current locals supply all prices; no mapping,
allocator room, successful store or minimum source clock is assumed. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer : BitVec 64) (n capacity depth target : Nat)
    (data : Locals source p buffer n capacity depth target) (installed : OriginalCode.Installed source.code)
    (positive : 1 ≤ capacity) (inside : n ≤ capacity) (small : 32*capacity + 32 < 2^64)
    (targetSmall : target < 2^63) (depths : depth ≤ target) :
    source.clock - (evaluateHOLFiniteState source afterBuffer).2.clock ≤ 44*capacity + 2*(target-depth) + 42 := by
  have composed : source.clock - (evaluateHOLFiniteState source afterBuffer).2.clock ≤
      CopyAny.price (32*n)+1 + (ZeroAny.price (32*(capacity-n))+1 + (3*(capacity-1)+(2*(target-depth)+43))) := by
    rw [source_shape.1]
    apply ClockCost.sequence_reached_current source _ afterCopy _ _ (copy_cost source p buffer n capacity depth target data installed (by omega))
    intro middle copied
    have next := data.after_call _ _ copied
    have nextCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none copied).2.2.2]; exact installed
    rw [source_shape.2.1]
    apply ClockCost.sequence_reached_current middle _ afterClear _ _ (zero_cost middle p buffer n capacity depth target next nextCode inside small)
    intro cleared zeroed
    have final := next.after_call _ _ zeroed
    have finalCode : OriginalCode.Installed cleared.code := by rw [(evaluation_fields middle cleared _ none zeroed).2.2.2]; exact nextCode
    exact after_clear_cost cleared p buffer n capacity depth target final finalCode positive (by omega) targetSmall depths
  unfold CopyAny.price ZeroAny.price at composed
  omega

end InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost.Locals.after_call
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost.copy_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost.zero_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost.after_clear_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleBufferCost.cost
