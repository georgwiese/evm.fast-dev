import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.CurrentHash.PackBytesCallCost
import InitECandidate.Solver.Input.CurrentHash.MerkleCallCost
import InitECandidate.Solver.Input.CurrentHash.FixedHashCost
import InitECandidate.Solver.Input.ClockCostScalarTerminating
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

namespace InitECandidate.Solver.Input.CurrentHash.BytesVectorCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body := Code.body .htr_bytes_vector
def long : ProgHOL 64 := match body with | .seq _ tail => tail | _ => .skip
def afterMark : ProgHOL 64 := match long with | .decCall _ _ _ _ tail => tail | _ => .skip
def afterPack : ProgHOL 64 := match afterMark with | .decCall _ _ _ _ tail => tail | _ => .skip
def afterMerkle : ProgHOL 64 := match afterPack with | .seq _ tail => tail | _ => .skip
def packArguments : List (ExpHOL 64) := [localVar "p", localVar "n"]
def merkleArguments : List (ExpHOL 64) := [.rfield 0 (localVar "pk"), .rfield 1 (localVar "pk"), .rfield 1 (localVar "pk"), localVar "out"]

set_option maxRecDepth 100000 in
theorem source_shape : long = .decCall (ofString "mark") .one (Code.name .heap_mark) [] afterMark ∧
    afterMark = .decCall (ofString "pk") PackBytes.returnShape (ofString "pack_bytes") packArguments afterPack ∧
    afterPack = .seq (.call (some (none, none)) (ofString "merkleize") merkleArguments) afterMerkle ∧
    afterMerkle = .seq (.call (some (none, none)) (Code.name .heap_release) [localVar "mark"]) (.return (.const 0#64)) := by
  simp only [body, long, afterMark, afterPack, afterMerkle, packArguments, merkleArguments, PackBytes.returnShape,
    Code.body, Code.entry, Code.declaration, Code.name, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_bytes_vector, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, localVar]
  exact ⟨True.intro, True.intro, True.intro, True.intro⟩

structure Params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat) : Prop where
  pointer : source.locals.lookup (ofString "p") = some (.val (.word p))
  length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))
  output : source.locals.lookup (ofString "out") = some (.val (.word out))

theorem suffix_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterMerkle 1 := by
  rw [source_shape.2.2.2]
  exact ClockCost.sequence code _ _ 1 0 (AllocatorCost.release_call code installed (some none) _) (ClockCost.returned code _)

theorem after_pack_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer out : BitVec 64) (n budget : Nat)
    (data : Params source p out n) (pk : source.locals.lookup (ofString "pk") = some (PackBytesReturn.tuple buffer n))
    (installed : OriginalCode.Installed source.code) (small : budget < 58)
    (chunksBound : PackBytes.chunks n ≤ 2^budget)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterPack = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*PackBytes.chunks n + 4*budget + 50 := by
  have upper : 2^budget ≤ 2^57 := Nat.pow_le_pow_right (by decide) (by omega)
  have number : (BitVec.ofNat 64 (PackBytes.chunks n)).toNat = PackBytes.chunks n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) merkleArguments =
      some (Merkle.values buffer (BitVec.ofNat 64 (PackBytes.chunks n)) (BitVec.ofNat 64 (PackBytes.chunks n)) out) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, merkleArguments, localVar, pk, PackBytesReturn.tuple, data.output, Merkle.values]
  rw [source_shape.2.2.1] at actual
  have composed := ClockCost.sequence_terminating source post _ afterMerkle (88*PackBytes.chunks n + 4*budget + 49) 1
    (by intro result target evaluated notTimeout
        have priced := MerkleCallCost.cost source target buffer (BitVec.ofNat 64 (PackBytes.chunks n)) (BitVec.ofNat 64 (PackBytes.chunks n)) out budget small
          (by rw [number]; exact chunksBound) (by rw [number]; exact chunksBound) installed (some none) merkleArguments args result evaluated notTimeout
        simpa only [number] using priced)
    (by intro middle continued result target evaluated notTimeout
        have codeEq := (evaluation_fields source middle _ none continued).2.2.2
        have paid := suffix_cost source.code installed middle codeEq
        rw [evaluated] at paid
        exact paid) result actual notTimeout
  omega

theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n budget : Nat)
    (data : Params source p out n) (installed : OriginalCode.Installed source.code)
    (lengthSmall : n + 64 < 2^64) (small : budget < 58)
    (chunksBound : PackBytes.chunks n ≤ 2^budget)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterMark = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + 51 := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) packArguments = some (PackBytes.values p n) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, packArguments, localVar, data.pointer, data.length, PackBytes.values]
  rw [source_shape.2.1] at actual
  have priced := PackBytesCallCost.scoped_cost_terminating source post p n installed lengthSmall "pk" packArguments afterPack
    (88*PackBytes.chunks n + 4*budget + 50) args (by
      intro target buffer codeEq result final evaluated notTimeout
      let entry := CallNormal.continuationEntry source target "pk" (PackBytesReturn.tuple buffer n)
      have kept (name : String) (different : ofString "pk" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
        simp [entry, CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, different, Ne.symm different]
      have next : Params entry p out n := ⟨(kept "p" (by decide)).trans data.pointer, (kept "n" (by decide)).trans data.length,
        (kept "out" (by decide)).trans data.output⟩
      have pk : entry.locals.lookup (ofString "pk") = some (PackBytesReturn.tuple buffer n) := by
        simp [entry, CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
      exact after_pack_cost entry final p buffer out n budget next pk currentCode small chunksBound result evaluated notTimeout)
    result actual notTimeout
  omega

/-- Actual vector long phase: mark, pack, Merkle and release. All current arguments and the actual returned packed count are derived at
this invocation; errors/traps remain included in the non-timeout observation. -/
theorem long_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n budget : Nat)
    (data : Params source p out n) (installed : OriginalCode.Installed source.code)
    (lengthSmall : n + 64 < 2^64) (small : budget < 58)
    (chunksBound : PackBytes.chunks n ≤ 2^budget)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source long = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + 52 := by
  rw [source_shape.1] at actual
  have priced := ClockCost.scalar_scope_terminating source post "mark" (Code.name .heap_mark) [] (Code.formals .heap_mark)
    (Code.body .heap_mark) afterMark (Code.shape .heap_mark) 0 (PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + 51)
    (Code.installed source.code installed .heap_mark) (StraightCost.body source.code .heap_mark (StraightCost.basic_supported .heap_mark (by simp)))
    (by intro target mark codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "mark" (.val (.word mark))
        have kept (name : String) (different : ofString "mark" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "mark" name mark different
        have next : Params entry p out n := ⟨(kept "p" (by decide)).trans data.pointer, (kept "n" (by decide)).trans data.length,
          (kept "out" (by decide)).trans data.output⟩
        have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
        exact after_mark_cost entry final p out n budget next currentCode lengthSmall small chunksBound result evaluated notTimeout)
    result actual notTimeout
  omega

def shortTest : ExpHOL 64 := .cmp .notLower (.const 32#64) (localVar "n")
def shortBody : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "memzero") [localVar "out", .const 32#64])
  (.seq (.call (some (none, none)) (ofString "memcpy") [localVar "out", localVar "p", localVar "n"]) (.return (.const 0#64)))
def shortGuard : ProgHOL 64 := .ite shortTest shortBody .skip

set_option maxRecDepth 100000 in
theorem body_shape : body = .seq shortGuard long := by
  simp only [body, long, shortGuard, shortTest, shortBody, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_bytes_vector,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar]

theorem Params.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {p out : BitVec 64} {n : Nat}
    (data : Params source p out n) (function : MlS) (arguments : List (ExpHOL 64))
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (none, post)) : Params post p out n := by
  have kept (name : MlS) : post.locals.lookup name = source.locals.lookup name := CallNormal.ignored_lookup source post name function arguments actual
  exact ⟨(kept _).trans data.pointer, (kept _).trans data.length, (kept _).trans data.output⟩

theorem short_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat)
    (data : Params source p out n) (installed : OriginalCode.Installed source.code) (small : n + 64 < 2^64) :
    source.clock - (evaluateHOLFiniteState source shortBody).2.clock ≤ CopyAny.price n + 43 := by
  unfold shortBody
  have zeroCost := FixedMemoryCost.zero source.code installed (some none) (localVar "out") 32 (by decide) source rfl
  have composed := ClockCost.sequence_reached_current source _ _ 42 (CopyAny.price n + 1) zeroCost (by
    intro middle zeroed
    have next := data.after_call _ _ zeroed
    have nextCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none zeroed).2.2.2]; exact installed
    have args : evalListHOLFinite middle (h := fun address => Classical.propDecidable (middle.memaddrs address))
        [localVar "out", localVar "p", localVar "n"] = some (CopyGeneral.values out p n) := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, next.output, next.pointer, next.length, CopyGeneral.values]
    exact ClockCost.sequence_current middle _ _ _ 0
      (MemoryCost.copy middle nextCode (some none) _ out p n (by omega) args) (ClockCost.returned middle.code (.const 0#64)))
  exact Nat.le_trans composed (by omega)

theorem guard_run (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat) (small : n < 2^64)
    (length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))) :
    evaluateHOLFiniteState source shortGuard = if n ≤ 32 then evaluateHOLFiniteState source shortBody else (none, source) := by
  have number : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have read : eval source shortTest = some (.val (.word (if n ≤ 32 then 1#64 else 0#64))) := by
    simp [eval, shortTest, localVar, evalHOLExact, toExact, length, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      BitVec.le_def, BitVec.lt_def, number]
  simp only [eval] at read
  rw [shortGuard, evaluateHOLFiniteState_ite, read]
  by_cases short : n ≤ 32
  · simp only [if_pos short]; rfl
  · simp only [if_neg short]; exact evaluateHOLFiniteState_skip source

/-- Complete current vector hashing, including its actual≤32byte early-return
branch. Long inputs use the same actual packed count for Merkle n and limit.
The allowance covers failed reads/stores/allocations and covered traps. -/
theorem cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n budget : Nat)
    (data : Params source p out n) (installed : OriginalCode.Installed source.code)
    (lengthSmall : n + 64 < 2^64) (small : budget < 58) (chunksBound : PackBytes.chunks n ≤ 2^budget)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + 52 := by
  by_cases short : n ≤ 32
  · have price := short_cost source p out n data installed lengthSmall
    have stopped : NoFallthrough shortBody := .sequence _ _ (.sequence _ _ (.returned _))
    have stops := stopped source
    rw [body_shape, evaluateHOLFiniteState_seq_line780, guard_run source n (by omega) data.length, if_pos short] at actual
    generalize computed : evaluateHOLFiniteState source shortBody = output at price stops actual
    obtain ⟨observed, middle⟩ := output
    cases observed with
    | none => exact False.elim (stops rfl)
    | some observed =>
      have endpoint := congrArg Prod.snd actual
      change middle = post at endpoint
      rw [endpoint] at price
      change source.clock - post.clock ≤ CopyAny.price n + 43 at price
      unfold PackBytesCost.price
      omega
  · rw [body_shape, StateSteps.next_sequence source source _ _
      (by rw [guard_run source n (by omega) data.length, if_neg short]) (Nat.le_refl _)] at actual
    exact long_cost source post p out n budget data installed lengthSmall small chunksBound result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.BytesVectorCost

#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.suffix_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.after_pack_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.long_cost

#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.body_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.Params.after_call
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.short_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.guard_run
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorCost.cost
