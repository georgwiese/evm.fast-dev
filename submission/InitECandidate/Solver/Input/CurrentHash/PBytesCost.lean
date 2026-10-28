import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.CurrentHash.PackBytesCallCost
import InitECandidate.Solver.Input.CurrentHash.PListCost
import InitECandidate.Solver.Input.CurrentHash.FixedHashCost
import InitECandidate.Solver.Input.ClockCostScalarTerminating
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.CurrentHash.PBytesCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body := Code.body .htr_pbytes
def afterMark : ProgHOL 64 := match body with | .decCall _ _ _ _ tail => tail | _ => .skip
def afterPack : ProgHOL 64 := match afterMark with | .decCall _ _ _ _ tail => tail | _ => .skip
def afterList : ProgHOL 64 := match afterPack with | .seq _ tail => tail | _ => .skip
def packArguments : List (ExpHOL 64) := [localVar "p", localVar "n"]
def listArguments : List (ExpHOL 64) := [.rfield 0 (localVar "pk"), .rfield 1 (localVar "pk"), localVar "n", localVar "out"]

set_option maxRecDepth 100000 in
theorem source_shape : body = .decCall (ofString "mark") .one (Code.name .heap_mark) [] afterMark ∧
    afterMark = .decCall (ofString "pk") PackBytes.returnShape (ofString "pack_bytes") packArguments afterPack ∧
    afterPack = .seq (.call (some (none, none)) (Code.name .htr_plist_chunks) listArguments) afterList ∧
    afterList = .seq (.call (some (none, none)) (Code.name .heap_release) [localVar "mark"]) (.return (.const 0#64)) := by
  simp only [body, afterMark, afterPack, afterList, packArguments, listArguments, PackBytes.returnShape,
    Code.body, Code.entry, Code.declaration, Code.name, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_pbytes, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, localVar]
  exact ⟨True.intro, True.intro, True.intro, True.intro⟩

structure Params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat) : Prop where
  pointer : source.locals.lookup (ofString "p") = some (.val (.word p))
  length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))
  output : source.locals.lookup (ofString "out") = some (.val (.word out))

theorem suffix_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterList 1 := by
  rw [source_shape.2.2.2]
  exact ClockCost.sequence code _ _ 1 0 (AllocatorCost.release_call code installed (some none) _) (ClockCost.returned code _)

theorem after_pack_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer out : BitVec 64) (n : Nat)
    (data : Params source p out n) (pk : source.locals.lookup (ofString "pk") = some (PackBytesReturn.tuple buffer n))
    (installed : OriginalCode.Installed source.code)
    (chunksBound : PackBytes.chunks n ≤ 134217728)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterPack = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*PackBytes.chunks n + 3170 := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) listArguments =
      some (PListCost.values buffer (BitVec.ofNat 64 n) out (PackBytes.chunks n)) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, listArguments, localVar, pk, PackBytesReturn.tuple, data.length, data.output, PListCost.values]
  rw [source_shape.2.2.1] at actual
  have composed := ClockCost.sequence_terminating source post _ afterList (88*PackBytes.chunks n + 3169) 1
    (by intro result target evaluated notTimeout
        exact PListCost.call_cost source target buffer (BitVec.ofNat 64 n) out (PackBytes.chunks n)
          chunksBound installed (some none) listArguments args result evaluated notTimeout)
    (by intro middle continued result target evaluated notTimeout
        have codeEq := (evaluation_fields source middle _ none continued).2.2.2
        have paid := suffix_cost source.code installed middle codeEq
        rw [evaluated] at paid
        exact paid) result actual notTimeout
  omega

theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat)
    (data : Params source p out n) (installed : OriginalCode.Installed source.code)
    (lengthSmall : n + 64 < 2^64)
    (chunksBound : PackBytes.chunks n ≤ 134217728)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterMark = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 3171 := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) packArguments = some (PackBytes.values p n) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, packArguments, localVar, data.pointer, data.length, PackBytes.values]
  rw [source_shape.2.1] at actual
  have priced := PackBytesCallCost.scoped_cost_terminating source post p n installed lengthSmall "pk" packArguments afterPack
    (88*PackBytes.chunks n + 3170) args (by
      intro target buffer codeEq result final evaluated notTimeout
      let entry := CallNormal.continuationEntry source target "pk" (PackBytesReturn.tuple buffer n)
      have kept (name : String) (different : ofString "pk" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
        simp [entry, CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, different, Ne.symm different]
      have next : Params entry p out n := ⟨(kept "p" (by decide)).trans data.pointer, (kept "n" (by decide)).trans data.length,
        (kept "out" (by decide)).trans data.output⟩
      have pk : entry.locals.lookup (ofString "pk") = some (PackBytesReturn.tuple buffer n) := by
        simp [entry, CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
      exact after_pack_cost entry final p buffer out n next pk currentCode chunksBound result evaluated notTimeout)
    result actual notTimeout
  omega

/-- Complete actual progressive-byte hashing, with the same returned packed
count and original byte length, including observed non-timeout errors/traps. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat)
    (data : Params source p out n) (installed : OriginalCode.Installed source.code)
    (lengthSmall : n + 64 < 2^64)
    (chunksBound : PackBytes.chunks n ≤ 134217728)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 3172 := by
  rw [source_shape.1] at actual
  have priced := ClockCost.scalar_scope_terminating source post "mark" (Code.name .heap_mark) [] (Code.formals .heap_mark)
    (Code.body .heap_mark) afterMark (Code.shape .heap_mark) 0 (PackBytesCost.price n + 88*PackBytes.chunks n + 3171)
    (Code.installed source.code installed .heap_mark) (StraightCost.body source.code .heap_mark (StraightCost.basic_supported .heap_mark (by simp)))
    (by intro target mark codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "mark" (.val (.word mark))
        have kept (name : String) (different : ofString "mark" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "mark" name mark different
        have next : Params entry p out n := ⟨(kept "p" (by decide)).trans data.pointer, (kept "n" (by decide)).trans data.length,
          (kept "out" (by decide)).trans data.output⟩
        have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
        exact after_mark_cost entry final p out n next currentCode lengthSmall chunksBound result evaluated notTimeout)
    result actual notTimeout
  omega

/-- Actual three-word progressive-byte caller, using its same checked callee
and the exact packed chunk count. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) (n : Nat)
    (installed : OriginalCode.Installed source.code) (lengthSmall : n + 64 < 2^64) (chunksBound : PackBytes.chunks n ≤ 134217728)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some (CallNormal.tripleValues p (BitVec.ofNat 64 n) out))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (Code.name .htr_pbytes) expressions) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 3173 := by
  have entry : source.code.lookup (Code.name .htr_pbytes) =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)], body, .one) := by
    simpa only [Code.formals, Code.body, Code.shape, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_pbytes, body, shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
      using Code.installed source.code installed .htr_pbytes
  obtain ⟨callee, called, pointer, length, output⟩ := CallNormal.triple_environment source.code.lookup (Code.name .htr_pbytes) body p (BitVec.ofNat 64 n) out entry
  exact ClockCost.call_current_terminating source post destination (Code.name .htr_pbytes) expressions (CallNormal.tripleValues p (BitVec.ofNat 64 n) out)
    body callee .one (PackBytesCost.price n + 88*PackBytes.chunks n + 3172) args called
    (fun result target evaluated notTimeout => body_cost (callEntryStateHOLFinite source callee) target p out n ⟨pointer, length, output⟩ installed lengthSmall chunksBound result evaluated notTimeout)
    result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.PBytesCost

#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesCost.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesCost.suffix_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesCost.after_pack_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesCost.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesCost.body_cost

#print axioms InitECandidate.Solver.Input.CurrentHash.PBytesCost.call_cost
