import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionRound
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Same actual current byte-hash call, protecting any earlier word outside
its real output and length workspace. All other temporary room is derived. -/
theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros query : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (data : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity) (active : index<n)
    (below : query.toNat<cursor.toNat) (rootsAway : CopyGeneral.Away roots query (32*n)) (chunkAway : CopyGeneral.Away chunk query 32)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") transactionArguments)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have context : MerkleMemory.Context source cursor zeros query := ⟨data.context.installed,data.context.domain,data.context.zeroCell,data.context.zeroArena,
    data.context.heap,data.context.heapLower,data.context.heapBound,data.context.aligned,below⟩
  have lengthBound:=geometry.lengthsBound index active
  have capacityBound:=geometry.capacityBound
  have chunksBound : PackBytes.chunks (lengths index)≤134217728 := by unfold PackBytes.chunks; omega
  exact PBytesMemory.call_frame source post (pointers index) cursor chunk (roots+BitVec.ofNat 64 (32*index)) zeros query (lengths index)
    context (by omega) chunksBound (geometry.inputs index active)
    (AllocatedBytes.Arena.subrange roots (32*n) (32*index) 32 geometry.rootsArena (by omega))
    (CopyGeneral.Away.subrange roots query (32*n) (32*index) 32 rootsAway (by omega))
    data.chunkCell geometry.chunkArena geometry.chunkAligned chunkAway transactionArguments
    (arguments_read source array roots cursor chunk zeros pointers lengths n capacity index data geometry active) actual

/-- Every physical decoded row survives the same real byte hash, including
rows to be read by subsequent iterations. -/
theorem call_metadata (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index offset : Nat)
    (data : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity) (active : index<n) (inside : offset<16*n)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") transactionArguments)=(none,post)) :
    post.memory (array+BitVec.ofNat 64 offset)=source.memory (array+BitVec.ofNat 64 offset) ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have positive : 0<n := by omega
  have arena := geometry.arrayArena positive
  let query := array+BitVec.ofNat 64 offset
  have number : query.toNat=array.toNat+offset := byteAddress_toNat array offset (by have h:=arena.upper; omega)
  have before : query.toNat<roots.toNat := by rw [number]; have h:=geometry.arrayBefore positive; omega
  have below : query.toNat<cursor.toNat := by have h:=geometry.rootsBefore; omega
  have rootsAway := CopyGeneral.Away.after roots query (32*n) geometry.rootsAligned (by have h:=geometry.rootsArena.upper; omega) before
  have chunkAway : CopyGeneral.Away chunk query 32 :=
    CopyGeneral.Away.before chunk query 32 array.toNat (geometry.chunkBefore positive) array.isLt (by rw [number]; omega)
  exact call_frame source post array roots cursor chunk zeros query pointers lengths n capacity index data geometry active below rootsAway chunkAway actual

/-- A real continuing hash retains the full decoded row image, caller
bindings, initialized workspace and actual entering heap. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (data : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity) (active : index<n)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") transactionArguments)=(none,post)) :
    RoundState post array roots cursor chunk zeros pointers lengths n index := by
  have heap := (call_metadata source post array roots cursor chunk zeros pointers lengths n capacity index 0 data geometry active (by omega) actual).2
  have context := data.context.after_call .htr_pbytes transactionArguments heap actual
  have other (name : String) := CallNormal.ignored_lookup source post (ofString name) (ofString "htr_pbytes") transactionArguments actual
  have image : Image post array pointers lengths n := by
    constructor
    intro selected bounded
    have pFrame := call_metadata source post array roots cursor chunk zeros pointers lengths n capacity index (16*selected) data geometry active (by omega) actual
    have nFrame := call_metadata source post array roots cursor chunk zeros pointers lengths n capacity index (16*selected+8) data geometry active (by omega) actual
    exact ⟨pFrame.1.trans (data.image.fields selected bounded).1,nFrame.1.trans (data.image.fields selected bounded).2⟩
  have global := Effects.call_preserves .lengthChunk source.code data.context.installed .htr_pbytes (some none) transactionArguments source rfl
  change GlobalEffects.erase (key .lengthChunk) (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") transactionArguments)).2=_ at global
  rw [actual] at global
  exact ⟨context,(other "txs").trans data.arrayLocal,(other "ntx").trans data.count,(other "roots").trans data.rootsLocal,(other "i").trans data.position,
    image,(congrArg Prod.snd global).trans data.chunkCell⟩

/-- The actual current increment advances one decoded transaction, retaining
all current metadata and arena/workspace facts for the next call. -/
theorem step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (data : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity) (active : index<n)
    (actual : evaluateHOLFiniteState source transactionStep=(none,post)) : RoundState post array roots cursor chunk zeros pointers lengths n (index+1) := by
  rw [loop_shapes.2.1] at actual
  obtain ⟨middle,normal,advanced⟩ := Input.sequence_none source post _ increment actual
  have current := call_normal source middle array roots cursor chunk zeros pointers lengths n capacity index data geometry active normal
  have read : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,current.position,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have endpoint := assign_none middle post "i" _ (BitVec.ofNat 64 (index+1)) read advanced
  rw [endpoint]
  exact ⟨current.context.of_frozen rfl,
    (bind_lookup_other middle "i" "txs" _ (by decide)).trans current.arrayLocal,
    (bind_lookup_other middle "i" "ntx" _ (by decide)).trans current.count,
    (bind_lookup_other middle "i" "roots" _ (by decide)).trans current.rootsLocal,bind_lookup_same _ _ _,⟨current.image.fields⟩,current.chunkCell⟩

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.call_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.call_metadata
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.call_normal
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.step_normal
