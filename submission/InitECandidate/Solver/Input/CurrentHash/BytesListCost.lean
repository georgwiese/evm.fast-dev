import InitECandidate.Solver.Input.CurrentHash.PackBytesCallCost
import InitECandidate.Solver.Input.CurrentHash.MerkleCallCost
import InitECandidate.Solver.Input.CurrentHash.FixedHashCost
import InitECandidate.Solver.Input.ClockCostScalarTerminating
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

namespace InitECandidate.Solver.Input.CurrentHash.BytesListCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body := Code.body .htr_bytes_list
def afterMark : ProgHOL 64 := match body with | .decCall _ _ _ _ tail => tail | _ => .skip
def afterPack : ProgHOL 64 := match afterMark with | .decCall _ _ _ _ tail => tail | _ => .skip
def afterMerkle : ProgHOL 64 := match afterPack with | .seq _ tail => tail | _ => .skip
def packArguments : List (ExpHOL 64) := [localVar "p", localVar "n"]
def merkleArguments : List (ExpHOL 64) := [.rfield 0 (localVar "pk"), .rfield 1 (localVar "pk"), localVar "limit_chunks", localVar "out"]

set_option maxRecDepth 100000 in
theorem source_shape : body = .decCall (ofString "mark") .one (Code.name .heap_mark) [] afterMark ∧
    afterMark = .decCall (ofString "pk") PackBytes.returnShape (ofString "pack_bytes") packArguments afterPack ∧
    afterPack = .seq (.call (some (none, none)) (ofString "merkleize") merkleArguments) afterMerkle ∧
    afterMerkle = .seq (.call (some (none, none)) (Code.name .heap_release) [localVar "mark"])
      (.seq (.call (some (none, none)) (Code.name .mix_in_length) [localVar "out", localVar "n", localVar "out"]) (.return (.const 0#64))) := by
  simp only [body, afterMark, afterPack, afterMerkle, packArguments, merkleArguments, PackBytes.returnShape,
    Code.body, Code.entry, Code.declaration, Code.name, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_bytes_list, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, localVar]
  exact ⟨True.intro, True.intro, True.intro, True.intro⟩

structure Params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p limit out : BitVec 64) (n : Nat) : Prop where
  pointer : source.locals.lookup (ofString "p") = some (.val (.word p))
  length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))
  maximum : source.locals.lookup (ofString "limit_chunks") = some (.val (.word limit))
  output : source.locals.lookup (ofString "out") = some (.val (.word out))

theorem suffix_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterMerkle 48 := by
  rw [source_shape.2.2.2]
  exact ClockCost.sequence code _ _ 1 47 (AllocatorCost.release_call code installed (some none) _)
    (ClockCost.sequence code _ _ 47 0 (FixedHashCost.mix_call code installed (some none) _) (ClockCost.returned code _))

theorem after_pack_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer limit out : BitVec 64) (n budget : Nat)
    (data : Params source p limit out n) (pk : source.locals.lookup (ofString "pk") = some (PackBytesReturn.tuple buffer n))
    (installed : OriginalCode.Installed source.code) (small : budget < 58)
    (chunksBound : PackBytes.chunks n ≤ 2^budget) (limitBound : limit.toNat ≤ 2^budget)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterPack = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*PackBytes.chunks n + 4*budget + 97 := by
  have upper : 2^budget ≤ 2^57 := Nat.pow_le_pow_right (by decide) (by omega)
  have number : (BitVec.ofNat 64 (PackBytes.chunks n)).toNat = PackBytes.chunks n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) merkleArguments =
      some (Merkle.values buffer (BitVec.ofNat 64 (PackBytes.chunks n)) limit out) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, merkleArguments, localVar, pk, PackBytesReturn.tuple, data.maximum, data.output, Merkle.values]
  rw [source_shape.2.2.1] at actual
  have composed := ClockCost.sequence_terminating source post _ afterMerkle (88*PackBytes.chunks n + 4*budget + 49) 48
    (by intro result target evaluated notTimeout
        have priced := MerkleCallCost.cost source target buffer (BitVec.ofNat 64 (PackBytes.chunks n)) limit out budget small
          (by rw [number]; exact chunksBound) limitBound installed (some none) merkleArguments args result evaluated notTimeout
        simpa only [number] using priced)
    (by intro middle continued result target evaluated notTimeout
        have codeEq := (evaluation_fields source middle _ none continued).2.2.2
        have paid := suffix_cost source.code installed middle codeEq
        rw [evaluated] at paid
        exact paid) result actual notTimeout
  omega

theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p limit out : BitVec 64) (n budget : Nat)
    (data : Params source p limit out n) (installed : OriginalCode.Installed source.code)
    (lengthSmall : n + 64 < 2^64) (small : budget < 58)
    (chunksBound : PackBytes.chunks n ≤ 2^budget) (limitBound : limit.toNat ≤ 2^budget)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterMark = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + 98 := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) packArguments = some (PackBytes.values p n) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, packArguments, localVar, data.pointer, data.length, PackBytes.values]
  rw [source_shape.2.1] at actual
  have priced := PackBytesCallCost.scoped_cost_terminating source post p n installed lengthSmall "pk" packArguments afterPack
    (88*PackBytes.chunks n + 4*budget + 97) args (by
      intro target buffer codeEq result final evaluated notTimeout
      let entry := CallNormal.continuationEntry source target "pk" (PackBytesReturn.tuple buffer n)
      have kept (name : String) (different : ofString "pk" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
        simp [entry, CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, different, Ne.symm different]
      have next : Params entry p limit out n := ⟨(kept "p" (by decide)).trans data.pointer, (kept "n" (by decide)).trans data.length,
        (kept "limit_chunks" (by decide)).trans data.maximum, (kept "out" (by decide)).trans data.output⟩
      have pk : entry.locals.lookup (ofString "pk") = some (PackBytesReturn.tuple buffer n) := by
        simp [entry, CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
      exact after_pack_cost entry final p buffer limit out n budget next pk currentCode small chunksBound limitBound result evaluated notTimeout)
    result actual notTimeout
  omega

/-- Complete actual bytes-list hashing: mark, pack, Merkle, release and length
mix. All current arguments and the actual returned packed count are derived at
this invocation; errors/traps remain included in the non-timeout observation. -/
theorem cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p limit out : BitVec 64) (n budget : Nat)
    (data : Params source p limit out n) (installed : OriginalCode.Installed source.code)
    (lengthSmall : n + 64 < 2^64) (small : budget < 58)
    (chunksBound : PackBytes.chunks n ≤ 2^budget) (limitBound : limit.toNat ≤ 2^budget)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + 99 := by
  rw [source_shape.1] at actual
  have priced := ClockCost.scalar_scope_terminating source post "mark" (Code.name .heap_mark) [] (Code.formals .heap_mark)
    (Code.body .heap_mark) afterMark (Code.shape .heap_mark) 0 (PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + 98)
    (Code.installed source.code installed .heap_mark) (StraightCost.body source.code .heap_mark (StraightCost.basic_supported .heap_mark (by simp)))
    (by intro target mark codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "mark" (.val (.word mark))
        have kept (name : String) (different : ofString "mark" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "mark" name mark different
        have next : Params entry p limit out n := ⟨(kept "p" (by decide)).trans data.pointer, (kept "n" (by decide)).trans data.length,
          (kept "limit_chunks" (by decide)).trans data.maximum, (kept "out" (by decide)).trans data.output⟩
        have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
        exact after_mark_cost entry final p limit out n budget next currentCode lengthSmall small chunksBound limitBound result evaluated notTimeout)
    result actual notTimeout
  omega

end InitECandidate.Solver.Input.CurrentHash.BytesListCost

#print axioms InitECandidate.Solver.Input.CurrentHash.BytesListCost.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesListCost.suffix_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesListCost.after_pack_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesListCost.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesListCost.cost
